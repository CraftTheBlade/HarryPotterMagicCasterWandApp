import asyncio
import json
import math
import os
import queue
import struct
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, colorchooser
from collections import defaultdict

from bleak import BleakScanner, BleakClient


WAND_NAME_PREFIX = "MCW"
COMMAND_CHAR = "57420002-587e-48a0-974c-544d6163c577"
NOTIFY_CHAR = "57420003-587e-48a0-974c-544d6163c577"
BATTERY_CHAR = "00002a19-0000-1000-8000-00805f9b34fb"

TRAINING_FILE = "wand_training.json"
CUSTOM_SPELLS_FILE = "custom_spells.json"

ACCEL_SCALE = 0.00048828125
GYRO_SCALE = 0.0010908308

INIT_COMMANDS = [
    bytes([0xDC, 0x00, 0x05]),
    bytes([0xDC, 0x01, 0x05]),
    bytes([0xDC, 0x02, 0x05]),
    bytes([0xDC, 0x03, 0x05]),
    bytes([0xDC, 0x04, 0x08]),
    bytes([0xDC, 0x05, 0x08]),
    bytes([0xDC, 0x06, 0x08]),
    bytes([0xDC, 0x07, 0x08]),
]

BUILTIN_SPELLS = {
    "Lumos": {
        "mode": "tip",
        "color": [255, 255, 255],
        "seconds": 8,
        "vibration_ms": 120,
    },
    "Protego": {
        "mode": "all",
        "color": [80, 160, 255],
        "seconds": 3,
        "vibration_ms": 220,
    },
    "Nox": {
        "mode": "off",
        "color": [0, 0, 0],
        "seconds": 4,
        "vibration_ms": 80,
    },
    "Expecto Patronum": {
        "mode": "patronus",
        "color": [0, 220, 255],
        "seconds": 7,
        "vibration_ms": 450,
    },
    "Avada Kedavra": {
        "mode": "slide_bottom_to_top",
        "color": [0, 255, 40],
        "seconds": 3,
        "vibration_ms": 550,
    },
}

LIGHT_MODES = [
    "tip",
    "all",
    "slide_bottom_to_top",
    "slide_top_to_bottom",
    "pulse",
    "off",
    "patronus",
]


class WandCore:
    def __init__(self, ui_queue):
        self.ui_queue = ui_queue
        self.loop = None
        self.loop_thread = None
        self.client = None
        self.wand_device = None
        self.connected = False
        self.connecting = False
        self.debug_enabled = False
        self.auto_reconnect = True
        self.stop_requested = False

        self.custom_spells = {}
        self.training_data = {
            "Lumos": [],
            "Protego": [],
            "Nox": [],
            "Expecto Patronum": [],
            "Avada Kedavra": [],
            "Unknown": [],
        }

        self.packet_counts = defaultdict(int)
        self.imu_packet_count = 0
        self.imu_sample_count = 0
        self.battery_percent = None
        self.last_spell = "None"
        self.last_guess = "None"

        self.baseline = {
            "gyro_x": 0.0,
            "gyro_y": 0.0,
            "gyro_z": 0.0,
            "accel_x": 0.0,
            "accel_y": 0.0,
            "accel_z": 0.0,
        }
        self.calibrating = False
        self.calibration_samples = []

        self.manual_recording = False
        self.manual_motion_samples = []
        self.last_motion_samples = []

        self.motion_buffer = []
        self.recording_motion = False
        self.last_motion_time = 0.0
        self.motion_started_time = 0.0

        self.current_light_task = None
        self.trigger_distance = 3.50
        self.min_confidence = 45
        self.auto_cast_enabled = True

        self.load_custom_spells()
        self.load_training()

    def start_loop(self):
        if self.loop_thread:
            return
        self.loop = asyncio.new_event_loop()
        self.loop_thread = threading.Thread(target=self._run_loop, daemon=True)
        self.loop_thread.start()

    def _run_loop(self):
        asyncio.set_event_loop(self.loop)
        self.loop.run_forever()

    def run_async(self, coro):
        self.start_loop()
        return asyncio.run_coroutine_threadsafe(coro, self.loop)

    def ui(self, event, data=None):
        self.ui_queue.put((event, data))

    def log(self, text, wand_output=False):
        if wand_output and not self.debug_enabled:
            return
        self.ui("log", text)

    def set_debug(self, enabled):
        self.debug_enabled = bool(enabled)
        self.log(f"Debug output {'ON' if enabled else 'OFF'}")

    def all_spell_configs(self):
        merged = {}
        merged.update(BUILTIN_SPELLS)
        merged.update(self.custom_spells)
        return merged

    def normalize_spell_name(self, name):
        if not name:
            return ""
        clean = name.lower().strip().replace("_", " ")
        aliases = {
            "lumos": "Lumos",
            "protego": "Protego",
            "protago": "Protego",
            "nox": "Nox",
            "expecto patronum": "Expecto Patronum",
            "expectopatronum": "Expecto Patronum",
            "patronum": "Expecto Patronum",
            "avada kedavra": "Avada Kedavra",
            "avadakedavra": "Avada Kedavra",
            "avada": "Avada Kedavra",
            "kedavra": "Avada Kedavra",
        }
        if clean in aliases:
            return aliases[clean]
        for spell in self.all_spell_configs().keys():
            if spell.lower().strip() == clean:
                return spell
        return name.strip()

    def load_custom_spells(self):
        if not os.path.exists(CUSTOM_SPELLS_FILE):
            self.custom_spells = {}
            return
        try:
            with open(CUSTOM_SPELLS_FILE, "r", encoding="utf-8") as f:
                self.custom_spells = json.load(f)
            for spell in self.custom_spells:
                self.training_data.setdefault(spell, [])
        except Exception as e:
            self.custom_spells = {}
            self.log(f"Could not load custom spells: {e}")

    def save_custom_spells(self):
        with open(CUSTOM_SPELLS_FILE, "w", encoding="utf-8") as f:
            json.dump(self.custom_spells, f, indent=2)

    def load_training(self):
        if not os.path.exists(TRAINING_FILE):
            return
        try:
            with open(TRAINING_FILE, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            for key, value in loaded.items():
                if isinstance(value, list):
                    self.training_data[key] = value
            for spell in self.all_spell_configs().keys():
                self.training_data.setdefault(spell, [])
            self.training_data.setdefault("Unknown", [])
        except Exception as e:
            self.log(f"Could not load training: {e}")

    def save_training(self):
        with open(TRAINING_FILE, "w", encoding="utf-8") as f:
            json.dump(self.training_data, f, indent=2)

    async def send_cmd(self, data: bytes, delay: float = 0.05):
        if not self.client or not self.client.is_connected:
            return
        try:
            await self.client.write_gatt_char(COMMAND_CHAR, data, response=False)
            await asyncio.sleep(delay)
        except Exception as e:
            self.log(f"Command write failed: {e}")

    async def find_wand(self):
        self.ui("status", "Scanning...")
        self.log("Scanning for Magic Caster Wand...")
        devices = await BleakScanner.discover(timeout=10)
        for d in devices:
            self.log(f"Found: {d.name} | {d.address}", wand_output=True)
            if d.name and d.name.startswith(WAND_NAME_PREFIX):
                return d
        return None

    async def connect(self):
        if self.connecting:
            return
        self.connecting = True
        self.stop_requested = False

        try:
            if self.client and self.client.is_connected:
                await self.disconnect()

            wand = await self.find_wand()
            if not wand:
                self.ui("status", "No wand found")
                self.log("No MCW wand found.")
                return

            self.wand_device = wand
            self.ui("status", f"Connecting to {wand.name}...")
            self.log(f"Connecting to {wand.name} / {wand.address}...")

            self.client = BleakClient(wand)
            await self.client.connect()
            self.connected = True
            self.ui("status", "Connected")
            self.log("Connected.")

            await self.client.start_notify(NOTIFY_CHAR, self.handle_notify)
            try:
                await self.client.start_notify(BATTERY_CHAR, self.handle_battery)
            except Exception:
                pass

            await asyncio.sleep(1.0)
            await self.init_wand()
            await self.start_imu_stream()
            await self.connected_effect()
            await self.led_off()
            await self.calibrate_wand_software(seconds=3)

            self.ui("spells_changed", None)
            self.run_async(self.monitor_connection())

        except Exception as e:
            self.connected = False
            self.ui("status", "Connection failed")
            self.log(f"Connection failed: {e}")
        finally:
            self.connecting = False

    async def reconnect(self):
        self.log("Reconnect requested.")
        await self.disconnect()
        await asyncio.sleep(1)
        await self.connect()

    async def disconnect(self):
        self.stop_requested = True
        try:
            self.stop_light_task()
            if self.client and self.client.is_connected:
                try:
                    await self.led_off()
                except Exception:
                    pass
                await self.client.disconnect()
        except Exception as e:
            self.log(f"Disconnect error: {e}")
        self.connected = False
        self.client = None
        self.ui("status", "Disconnected")

    async def monitor_connection(self):
        while self.client and self.client.is_connected and not self.stop_requested:
            await asyncio.sleep(1)
        if not self.stop_requested and self.auto_reconnect:
            self.connected = False
            self.ui("status", "Disconnected. Reconnecting...")
            self.log("Wand disconnected. Auto-reconnecting...")
            await asyncio.sleep(2)
            await self.connect()

    async def init_wand(self):
        self.log("Initializing wand...")
        for cmd in INIT_COMMANDS:
            await self.send_cmd(cmd, delay=0.08)
        self.log("Wand ready.")

    async def start_imu_stream(self):
        await self.send_cmd(bytes([0x31]), delay=0.20)
        await self.send_cmd(bytes([0x30, 0x00, 0x80]), delay=0.20)
        await self.send_cmd(bytes([0x31]), delay=0.20)
        await self.send_cmd(bytes([0x30, 0x00, 0x80]), delay=0.20)
        self.log("IMU stream enabled.")

    async def stop_imu_stream(self):
        await self.send_cmd(bytes([0x31]), delay=0.10)

    async def vibrate(self, duration_ms=350):
        duration_ms = max(0, min(2000, int(duration_ms)))
        if duration_ms <= 0:
            return
        packet = bytes([0x68, 0x50]) + struct.pack("<H", duration_ms)
        await self.send_cmd(packet, delay=0.08)

    async def double_buzz(self):
        await self.vibrate(90)
        await asyncio.sleep(0.12)
        await self.vibrate(90)

    async def led_off(self):
        await self.send_cmd(bytes([0x40]), delay=0.02)

    async def led_color(self, group: int, r: int, g: int, b: int):
        await self.send_cmd(
            bytes([
                0x42,
                group & 0xFF,
                max(0, min(255, int(r))),
                max(0, min(255, int(g))),
                max(0, min(255, int(b))),
            ]),
            delay=0.02,
        )

    async def set_all_leds(self, r: int, g: int, b: int):
        await self.led_color(0x00, r, g, b)
        await self.led_color(0x01, r, g, b)
        await self.led_color(0x02, r, g, b)
        await self.led_color(0x03, r, g, b)

    async def connected_effect(self):
        await self.vibrate(350)
        end_time = asyncio.get_event_loop().time() + 2.0
        while asyncio.get_event_loop().time() < end_time:
            await self.set_all_leds(40, 120, 255)
            await asyncio.sleep(0.25)
        await self.led_off()

    def start_light_task(self, coro):
        self.stop_light_task()
        self.current_light_task = asyncio.create_task(coro)

    def stop_light_task(self):
        if self.current_light_task and not self.current_light_task.done():
            self.current_light_task.cancel()
        self.current_light_task = None

    async def listening_effect(self):
        while True:
            await self.set_all_leds(0, 255, 255)
            await asyncio.sleep(0.25)

    async def keep_leds_off(self, seconds=3):
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.led_off()
            await asyncio.sleep(0.30)

    async def effect_tip(self, color, seconds, vibration_ms=0):
        await self.vibrate(vibration_ms)
        r, g, b = color
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.led_off()
            await self.led_color(0x00, r, g, b)
            await asyncio.sleep(0.25)

    async def effect_all(self, color, seconds, vibration_ms=0):
        await self.vibrate(vibration_ms)
        r, g, b = color
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.set_all_leds(r, g, b)
            await asyncio.sleep(0.30)

    async def effect_slide_bottom_to_top(self, color, seconds, vibration_ms=0):
        await self.vibrate(vibration_ms)
        r, g, b = color
        dim = [int(r * 0.35), int(g * 0.35), int(b * 0.35)]
        mid = [int(r * 0.70), int(g * 0.70), int(b * 0.70)]
        bright = [r, g, b]
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.led_off()
            await self.led_color(0x03, *dim)
            await asyncio.sleep(0.12)
            await self.led_color(0x02, *mid)
            await asyncio.sleep(0.12)
            await self.led_color(0x01, *bright)
            await asyncio.sleep(0.12)
            await self.led_color(0x00, *bright)
            await asyncio.sleep(0.35)
            await self.set_all_leds(*bright)
            await asyncio.sleep(0.35)

    async def effect_slide_top_to_bottom(self, color, seconds, vibration_ms=0):
        await self.vibrate(vibration_ms)
        r, g, b = color
        dim = [int(r * 0.35), int(g * 0.35), int(b * 0.35)]
        mid = [int(r * 0.70), int(g * 0.70), int(b * 0.70)]
        bright = [r, g, b]
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.led_off()
            await self.led_color(0x00, *bright)
            await asyncio.sleep(0.12)
            await self.led_color(0x01, *bright)
            await asyncio.sleep(0.12)
            await self.led_color(0x02, *mid)
            await asyncio.sleep(0.12)
            await self.led_color(0x03, *dim)
            await asyncio.sleep(0.35)
            await self.set_all_leds(*bright)
            await asyncio.sleep(0.35)

    async def effect_pulse(self, color, seconds, vibration_ms=0):
        await self.vibrate(vibration_ms)
        r, g, b = color
        low = [int(r * 0.25), int(g * 0.25), int(b * 0.25)]
        high = [r, g, b]
        pulse_high = False
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            pulse_high = not pulse_high
            await self.set_all_leds(*(high if pulse_high else low))
            await asyncio.sleep(0.25)

    async def effect_patronus(self, seconds=7, vibration_ms=450):
        await self.vibrate(vibration_ms)
        end_time = asyncio.get_event_loop().time() + seconds
        dark_blue = (0, 35, 160)
        medium_blue = (0, 90, 220)
        cyan = (0, 220, 255)
        pale_cyan = (120, 255, 255)
        while asyncio.get_event_loop().time() < end_time:
            await self.led_off()
            await self.led_color(0x03, *dark_blue)
            await asyncio.sleep(0.10)
            await self.led_color(0x02, *medium_blue)
            await asyncio.sleep(0.10)
            await self.led_color(0x01, *cyan)
            await asyncio.sleep(0.10)
            await self.led_color(0x00, *pale_cyan)
            await asyncio.sleep(0.18)
            await self.set_all_leds(0, 80, 220)
            await asyncio.sleep(0.18)
            await self.set_all_leds(0, 180, 255)
            await asyncio.sleep(0.18)

    async def failed_cast_light(self, seconds=1.2):
        await self.double_buzz()
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.set_all_leds(255, 60, 30)
            await asyncio.sleep(0.12)
            await self.led_off()
            await asyncio.sleep(0.12)

    async def learned_cast_light(self, seconds=1.0):
        await self.vibrate(150)
        end_time = asyncio.get_event_loop().time() + seconds
        while asyncio.get_event_loop().time() < end_time:
            await self.set_all_leds(120, 0, 255)
            await asyncio.sleep(0.20)

    def run_spell_action(self, spell: str, source="AI"):
        spell = self.normalize_spell_name(spell)
        config = self.all_spell_configs().get(spell)
        self.last_spell = spell
        self.ui("last_spell", spell)
        self.log(f"CASTING: {spell} ({source})")
        if not self.client or not self.client.is_connected:
            self.log("Cannot cast: wand is not connected.")
            return
        if not config:
            self.start_light_task(self.learned_cast_light(1.0))
            return

        mode = config.get("mode", "all")
        color = config.get("color", [255, 255, 255])
        seconds = float(config.get("seconds", 4))
        vibration_ms = int(config.get("vibration_ms", 0))

        if mode == "tip":
            self.start_light_task(self.effect_tip(color, seconds, vibration_ms))
        elif mode == "all":
            self.start_light_task(self.effect_all(color, seconds, vibration_ms))
        elif mode == "slide_bottom_to_top":
            self.start_light_task(self.effect_slide_bottom_to_top(color, seconds, vibration_ms))
        elif mode == "slide_top_to_bottom":
            self.start_light_task(self.effect_slide_top_to_bottom(color, seconds, vibration_ms))
        elif mode == "pulse":
            self.start_light_task(self.effect_pulse(color, seconds, vibration_ms))
        elif mode == "off":
            async def off_effect():
                await self.vibrate(vibration_ms)
                await self.keep_leds_off(seconds)
            self.start_light_task(off_effect())
        elif mode == "patronus":
            self.start_light_task(self.effect_patronus(seconds, vibration_ms))
        else:
            self.start_light_task(self.effect_all(color, seconds, vibration_ms))

    def motion_magnitude(self, sample):
        gx, gy, gz, ax, ay, az = sample
        gyro_mag = math.sqrt(gx * gx + gy * gy + gz * gz)
        accel_mag = math.sqrt(ax * ax + ay * ay + az * az)
        return gyro_mag + accel_mag * 2.0

    def subtract_baseline(self, sample):
        gx, gy, gz, ax, ay, az = sample
        return (
            gx - self.baseline["gyro_x"],
            gy - self.baseline["gyro_y"],
            gz - self.baseline["gyro_z"],
            ax - self.baseline["accel_x"],
            ay - self.baseline["accel_y"],
            az - self.baseline["accel_z"],
        )

    def resample_sequence(self, seq, target_len=40):
        if not seq:
            return []
        if len(seq) == 1:
            return [seq[0]] * target_len
        result = []
        for i in range(target_len):
            pos = i * (len(seq) - 1) / (target_len - 1)
            left = int(math.floor(pos))
            right = min(left + 1, len(seq) - 1)
            t = pos - left
            a = seq[left]
            b = seq[right]
            result.append(tuple(a[j] * (1 - t) + b[j] * t for j in range(len(a))))
        return result

    def normalize_sequence(self, seq):
        if not seq:
            return []
        dims = len(seq[0])
        means = [sum(x[d] for x in seq) / len(seq) for d in range(dims)]
        centered = [tuple(x[d] - means[d] for d in range(dims)) for x in seq]
        total_energy = sum(value * value for x in centered for value in x)
        scale = math.sqrt(total_energy / max(1, len(centered)))
        if scale < 0.0001:
            return centered
        return [tuple(value / scale for value in x) for x in centered]

    def prepare_motion_template(self, samples):
        if len(samples) < 6:
            return []
        cleaned = [self.subtract_baseline(s) for s in samples]
        while cleaned and self.motion_magnitude(cleaned[0]) < 0.03:
            cleaned.pop(0)
        while cleaned and self.motion_magnitude(cleaned[-1]) < 0.03:
            cleaned.pop()
        if len(cleaned) < 6:
            return []
        seq = self.normalize_sequence(cleaned)
        seq = self.resample_sequence(seq, target_len=40)
        return [list(x) for x in seq]

    def template_distance(self, a, b):
        if not a or not b:
            return 999999.0
        count = min(len(a), len(b))
        total = 0.0
        for i in range(count):
            dims = min(len(a[i]), len(b[i]))
            diff = sum((a[i][j] - b[i][j]) ** 2 for j in range(dims))
            total += math.sqrt(diff)
        return total / count

    def add_training_example(self, spell_name, samples=None):
        spell_name = self.normalize_spell_name(spell_name)
        samples = samples if samples is not None else self.last_motion_samples
        if not samples:
            self.log("No last motion to save. Do a wand movement first.")
            self.ui("toast", "No motion to train yet.")
            return False
        template = self.prepare_motion_template(samples)
        if not template:
            self.log(f"Motion too short/weak to save. Raw samples: {len(samples)}")
            self.ui("toast", "Motion too short/weak.")
            return False
        self.training_data.setdefault(spell_name, [])
        self.training_data[spell_name].append(template)
        self.training_data[spell_name] = self.training_data[spell_name][-30:]
        self.save_training()
        self.log(f"Saved last motion as {spell_name}. Examples: {len(self.training_data[spell_name])}")
        self.ui("training_updated", None)
        return True

    def get_trained_spell_count(self):
        return sum(1 for spell, examples in self.training_data.items() if spell != "Unknown" and examples)

    def classify_motion(self, samples):
        template = self.prepare_motion_template(samples)
        if not template:
            return None, []
        spell_distances = []
        for spell, examples in self.training_data.items():
            if spell == "Unknown" or spell not in self.all_spell_configs() or not examples:
                continue
            distances = [self.template_distance(template, ex) for ex in examples]
            distances.sort()
            best_few = distances[:3]
            distance = sum(best_few) / len(best_few)
            spell_distances.append((spell, distance))
        if not spell_distances:
            return None, []
        spell_distances.sort(key=lambda x: x[1])
        raw_scores = [(spell, 1.0 / ((dist * dist) + 0.001), dist) for spell, dist in spell_distances]
        total = sum(score for _, score, _ in raw_scores)
        results = [(spell, round((score / total) * 100), dist) for spell, score, dist in raw_scores]
        return results[0][0], results

    def maybe_auto_cast(self, samples):
        if not samples:
            self.log("No motion samples to classify.")
            return
        best_spell, guesses = self.classify_motion(samples)
        if not guesses:
            self.log("AI guess: no learned spell examples yet.")
            if self.client and self.client.is_connected:
                self.start_light_task(self.failed_cast_light())
            return
        lines = [f"{spell}: {percent}%" for spell, percent, _ in guesses[:5]]
        self.last_guess = " | ".join(lines)
        self.ui("last_guess", self.last_guess)
        self.log("AI movement guess: " + self.last_guess)
        if not self.auto_cast_enabled:
            return
        best_name, best_percent, best_distance = guesses[0]
        if self.get_trained_spell_count() == 1:
            should_cast = best_distance <= self.trigger_distance
        else:
            should_cast = best_percent >= self.min_confidence and best_distance <= self.trigger_distance
        if should_cast:
            self.run_spell_action(best_spell, source="AI learned")
        else:
            self.log("AI did not cast. Train more examples or make AI easier.")
            if self.client and self.client.is_connected:
                self.start_light_task(self.failed_cast_light())

    async def calibrate_wand_software(self, seconds=3):
        self.log(f"Calibration: keep wand still for {seconds} seconds...")
        self.calibration_samples = []
        self.calibrating = True
        await asyncio.sleep(seconds + 0.2)
        self.calibrating = False
        if len(self.calibration_samples) < 5:
            self.log("Calibration failed: not enough IMU samples.")
            return
        dims = list(zip(*self.calibration_samples))
        self.baseline = {
            "gyro_x": sum(dims[0]) / len(dims[0]),
            "gyro_y": sum(dims[1]) / len(dims[1]),
            "gyro_z": sum(dims[2]) / len(dims[2]),
            "accel_x": sum(dims[3]) / len(dims[3]),
            "accel_y": sum(dims[4]) / len(dims[4]),
            "accel_z": sum(dims[5]) / len(dims[5]),
        }
        self.log("Calibration complete.")
        if self.client and self.client.is_connected:
            self.start_light_task(self.learned_cast_light(1.0))

    def finish_manual_cast(self):
        if not self.manual_motion_samples:
            self.log("Cast ended, but no IMU samples were recorded.")
            return
        self.last_motion_samples = list(self.manual_motion_samples)
        self.log(f"Motion saved. Samples: {len(self.last_motion_samples)}")
        self.ui("motion_saved", len(self.last_motion_samples))
        self.maybe_auto_cast(self.last_motion_samples)

    def handle_button_packet(self, mask: int):
        all_buttons = (mask & 0x0F) == 0x0F
        no_buttons = (mask & 0x0F) == 0x00
        if all_buttons and not self.manual_recording:
            self.log("Cast recording started.")
            self.manual_recording = True
            self.manual_motion_samples = []
            if self.client and self.client.is_connected:
                self.start_light_task(self.listening_effect())
        elif no_buttons and self.manual_recording:
            self.log("Cast recording ended.")
            self.manual_recording = False
            if self.client and self.client.is_connected:
                self.start_light_task(self.keep_leds_off(1))
            self.finish_manual_cast()

    def parse_imu_payload(self, data: bytearray):
        if len(data) < 4:
            return
        sample_count = data[3]
        expected_length = 4 + sample_count * 12
        if len(data) < expected_length:
            return
        self.imu_packet_count += 1
        offset = 4
        for _ in range(sample_count):
            try:
                gyro_x, gyro_y, gyro_z, accel_x, accel_y, accel_z = struct.unpack_from("<hhhhhh", data, offset)
                offset += 12
                raw_sample = (
                    gyro_x * GYRO_SCALE,
                    gyro_y * GYRO_SCALE,
                    gyro_z * GYRO_SCALE,
                    accel_x * ACCEL_SCALE,
                    accel_y * ACCEL_SCALE,
                    accel_z * ACCEL_SCALE,
                )
                self.imu_sample_count += 1
                if self.calibrating:
                    self.calibration_samples.append(raw_sample)
                    continue
                if self.manual_recording:
                    self.manual_motion_samples.append(raw_sample)
                sample = self.subtract_baseline(raw_sample)
                mag = self.motion_magnitude(sample)
                now = time.time()
                moving = mag > 0.12
                if moving and not self.recording_motion:
                    self.recording_motion = True
                    self.motion_started_time = now
                    self.motion_buffer = []
                if self.recording_motion:
                    self.motion_buffer.append(raw_sample)
                    self.last_motion_time = now
                    if len(self.motion_buffer) > 700:
                        self.motion_buffer = self.motion_buffer[-700:]
                if self.recording_motion and (now - self.last_motion_time) > 0.7:
                    self.recording_motion = False
                    if not self.manual_recording and len(self.motion_buffer) >= 8:
                        self.last_motion_samples = list(self.motion_buffer)
            except Exception:
                return

    def handle_notify(self, sender, data: bytearray):
        if not data:
            return
        opcode = data[0]
        self.packet_counts[opcode] += 1
        self.log(f"RAW opcode=0x{opcode:02X} len={len(data)} data={data.hex(' ')}", wand_output=True)
        if len(data) >= 5 and data[0] == 0x24:
            text_len = data[3]
            if len(data) >= 4 + text_len:
                try:
                    spell = data[4:4 + text_len].decode("utf-8", errors="ignore")
                    spell = spell.replace("\x00", "").replace("_", " ").strip()
                    spell = self.normalize_spell_name(spell)
                    if spell:
                        self.log(f"Official spell detected: {spell}")
                        if self.last_motion_samples:
                            self.add_training_example(spell, self.last_motion_samples)
                        self.run_spell_action(spell, source="official wand")
                        return
                except Exception:
                    pass
        if len(data) >= 2 and data[0] == 0x10:
            self.handle_button_packet(data[1])
            return
        if len(data) >= 4 and data[0] == 0x2C:
            self.parse_imu_payload(data)
            return

    def handle_battery(self, sender, data: bytearray):
        if data:
            self.battery_percent = int(data[0])
            self.ui("battery", self.battery_percent)

    def add_custom_spell(self, name, mode, color, seconds, vibration_ms):
        name = self.normalize_spell_name(name)
        if not name:
            raise ValueError("Spell name cannot be empty.")
        self.custom_spells[name] = {
            "mode": mode,
            "color": color,
            "seconds": float(seconds),
            "vibration_ms": int(vibration_ms),
        }
        self.training_data.setdefault(name, [])
        self.save_custom_spells()
        self.save_training()
        self.ui("spells_changed", None)
        self.log(f"Added custom spell: {name}")


class AddSpellDialog(tk.Toplevel):
    def __init__(self, parent, on_save):
        super().__init__(parent)
        self.title("Add Custom Spell")
        self.resizable(False, False)
        self.on_save = on_save
        self.color = [0, 255, 255]

        self.name_var = tk.StringVar()
        self.mode_var = tk.StringVar(value="all")
        self.seconds_var = tk.StringVar(value="4")
        self.vibration_var = tk.StringVar(value="150")
        self.use_vibration_var = tk.BooleanVar(value=True)
        self.color_text_var = tk.StringVar(value="0, 255, 255")

        frm = ttk.Frame(self, padding=12)
        frm.grid(row=0, column=0, sticky="nsew")

        ttk.Label(frm, text="Spell name:").grid(row=0, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.name_var, width=30).grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Light movement:").grid(row=1, column=0, sticky="w", pady=4)
        ttk.Combobox(frm, textvariable=self.mode_var, values=LIGHT_MODES, state="readonly", width=27).grid(row=1, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Color:").grid(row=2, column=0, sticky="w", pady=4)
        color_row = ttk.Frame(frm)
        color_row.grid(row=2, column=1, sticky="ew", pady=4)
        ttk.Entry(color_row, textvariable=self.color_text_var, width=18).pack(side="left")
        ttk.Button(color_row, text="Pick", command=self.pick_color).pack(side="left", padx=5)

        ttk.Label(frm, text="Duration seconds:").grid(row=3, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.seconds_var, width=30).grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Checkbutton(frm, text="Use vibration", variable=self.use_vibration_var).grid(row=4, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.vibration_var, width=30).grid(row=4, column=1, sticky="ew", pady=4)

        btns = ttk.Frame(frm)
        btns.grid(row=5, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right", padx=4)
        ttk.Button(btns, text="Save", command=self.save).pack(side="right", padx=4)

        self.grab_set()
        self.transient(parent)

    def pick_color(self):
        chosen = colorchooser.askcolor(color="#00ffff", parent=self)
        if chosen and chosen[0]:
            r, g, b = [int(v) for v in chosen[0]]
            self.color = [r, g, b]
            self.color_text_var.set(f"{r}, {g}, {b}")

    def parse_color(self):
        text = self.color_text_var.get().strip()
        if text.startswith("#") and len(text) == 7:
            return [int(text[1:3], 16), int(text[3:5], 16), int(text[5:7], 16)]
        parts = text.replace(",", " ").split()
        if len(parts) == 3:
            return [max(0, min(255, int(parts[0]))), max(0, min(255, int(parts[1]))), max(0, min(255, int(parts[2])))]
        return self.color

    def save(self):
        try:
            name = self.name_var.get().strip()
            mode = self.mode_var.get().strip()
            color = self.parse_color()
            seconds = float(self.seconds_var.get().strip())
            vibration_ms = int(self.vibration_var.get().strip()) if self.use_vibration_var.get() else 0
            self.on_save(name, mode, color, seconds, vibration_ms)
            self.destroy()
        except Exception as e:
            messagebox.showerror("Invalid spell", str(e), parent=self)


class MagicCasterGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Magic Caster Wand AI Controller")
        self.geometry("980x700")
        self.minsize(850, 600)

        self.ui_queue = queue.Queue()
        self.core = WandCore(self.ui_queue)
        self.core.start_loop()

        self.debug_var = tk.BooleanVar(value=False)
        self.training_visible = tk.BooleanVar(value=True)
        self.status_var = tk.StringVar(value="Disconnected")
        self.battery_var = tk.StringVar(value="Battery: ?")
        self.last_spell_var = tk.StringVar(value="Last spell: None")
        self.last_guess_var = tk.StringVar(value="AI guess: None")
        self.samples_var = tk.StringVar(value="Samples: 0")

        self.build_ui()
        self.refresh_training_buttons()
        self.after(100, self.process_ui_queue)

    def build_ui(self):
        root = ttk.Frame(self, padding=10)
        root.pack(fill="both", expand=True)

        top = ttk.Frame(root)
        top.pack(fill="x")

        ttk.Label(top, text="Magic Caster Wand", font=("Segoe UI", 18, "bold")).pack(side="left")
        ttk.Label(top, textvariable=self.status_var, font=("Segoe UI", 11)).pack(side="right", padx=8)

        controls = ttk.LabelFrame(root, text="Connection", padding=10)
        controls.pack(fill="x", pady=8)

        ttk.Button(controls, text="Connect", command=self.connect).pack(side="left", padx=4)
        ttk.Button(controls, text="Reconnect", command=self.reconnect).pack(side="left", padx=4)
        ttk.Button(controls, text="Disconnect", command=self.disconnect).pack(side="left", padx=4)
        ttk.Button(controls, text="Restart IMU", command=self.restart_imu).pack(side="left", padx=4)
        ttk.Button(controls, text="Calibrate", command=self.calibrate).pack(side="left", padx=4)
        ttk.Button(controls, text="Vibrate Test", command=self.vibrate_test).pack(side="left", padx=4)

        ttk.Checkbutton(controls, text="Debug wand output", variable=self.debug_var, command=self.toggle_debug).pack(side="left", padx=12)
        ttk.Checkbutton(controls, text="Show training", variable=self.training_visible, command=self.toggle_training).pack(side="left", padx=4)
        ttk.Label(controls, textvariable=self.battery_var).pack(side="right")

        info = ttk.LabelFrame(root, text="Live", padding=10)
        info.pack(fill="x", pady=8)
        ttk.Label(info, textvariable=self.last_spell_var).grid(row=0, column=0, sticky="w", padx=5, pady=2)
        ttk.Label(info, textvariable=self.last_guess_var).grid(row=1, column=0, sticky="w", padx=5, pady=2)
        ttk.Label(info, textvariable=self.samples_var).grid(row=2, column=0, sticky="w", padx=5, pady=2)

        actions = ttk.LabelFrame(root, text="Manual Effects", padding=10)
        actions.pack(fill="x", pady=8)
        ttk.Button(actions, text="Lumos", command=lambda: self.manual_effect("Lumos")).pack(side="left", padx=3)
        ttk.Button(actions, text="Protego", command=lambda: self.manual_effect("Protego")).pack(side="left", padx=3)
        ttk.Button(actions, text="Nox", command=lambda: self.manual_effect("Nox")).pack(side="left", padx=3)
        ttk.Button(actions, text="Expecto Patronum", command=lambda: self.manual_effect("Expecto Patronum")).pack(side="left", padx=3)
        ttk.Button(actions, text="Avada Kedavra", command=lambda: self.manual_effect("Avada Kedavra")).pack(side="left", padx=3)
        ttk.Button(actions, text="Add New Spell", command=self.add_spell).pack(side="right", padx=3)

        self.training_frame = ttk.LabelFrame(root, text="Training", padding=10)
        self.training_frame.pack(fill="x", pady=8)

        log_frame = ttk.LabelFrame(root, text="Log", padding=6)
        log_frame.pack(fill="both", expand=True, pady=8)
        self.log_text = tk.Text(log_frame, height=14, wrap="word", state="disabled")
        self.log_text.pack(side="left", fill="both", expand=True)
        scroll = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_text.yview)
        scroll.pack(side="right", fill="y")
        self.log_text.configure(yscrollcommand=scroll.set)

    def refresh_training_buttons(self):
        for child in self.training_frame.winfo_children():
            child.destroy()

        row = 0
        col = 0
        for spell in self.core.all_spell_configs().keys():
            count = len(self.core.training_data.get(spell, []))
            text = f"Train {spell} ({count})"
            btn = ttk.Button(self.training_frame, text=text, command=lambda s=spell: self.train_spell(s))
            btn.grid(row=row, column=col, padx=4, pady=4, sticky="ew")
            col += 1
            if col >= 3:
                col = 0
                row += 1

        ttk.Button(self.training_frame, text="Train Unknown / Bad Motion", command=lambda: self.train_spell("Unknown")).grid(row=row + 1, column=0, padx=4, pady=4, sticky="ew")
        ttk.Button(self.training_frame, text="Show Counts", command=self.show_counts).grid(row=row + 1, column=1, padx=4, pady=4, sticky="ew")
        ttk.Button(self.training_frame, text="Add New Spell", command=self.add_spell).grid(row=row + 1, column=2, padx=4, pady=4, sticky="ew")

    def toggle_training(self):
        if self.training_visible.get():
            self.training_frame.pack(fill="x", pady=8, before=self.children[next(reversed(self.children))] if False else None)
        else:
            self.training_frame.pack_forget()

    def toggle_debug(self):
        self.core.set_debug(self.debug_var.get())

    def connect(self):
        self.core.run_async(self.core.connect())

    def reconnect(self):
        self.core.run_async(self.core.reconnect())

    def disconnect(self):
        self.core.run_async(self.core.disconnect())

    def restart_imu(self):
        self.core.run_async(self.core.start_imu_stream())

    def calibrate(self):
        self.core.run_async(self.core.calibrate_wand_software(3))

    def vibrate_test(self):
        self.core.run_async(self.core.vibrate(350))

    def manual_effect(self, spell):
        self.core.run_async(self._manual_effect_async(spell))

    async def _manual_effect_async(self, spell):
        self.core.run_spell_action(spell, source="GUI manual")

    def train_spell(self, spell):
        ok = self.core.add_training_example(spell)
        if ok:
            self.refresh_training_buttons()

    def show_counts(self):
        lines = []
        for spell in self.core.all_spell_configs().keys():
            lines.append(f"{spell}: {len(self.core.training_data.get(spell, []))}")
        lines.append(f"Unknown: {len(self.core.training_data.get('Unknown', []))}")
        messagebox.showinfo("Training Counts", "\n".join(lines), parent=self)

    def add_spell(self):
        AddSpellDialog(self, self.save_new_spell)

    def save_new_spell(self, name, mode, color, seconds, vibration_ms):
        self.core.add_custom_spell(name, mode, color, seconds, vibration_ms)
        self.refresh_training_buttons()

    def append_log(self, text):
        self.log_text.configure(state="normal")
        self.log_text.insert("end", text + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def process_ui_queue(self):
        try:
            while True:
                event, data = self.ui_queue.get_nowait()
                if event == "log":
                    self.append_log(str(data))
                elif event == "status":
                    self.status_var.set(str(data))
                elif event == "battery":
                    self.battery_var.set(f"Battery: {data}%")
                elif event == "last_spell":
                    self.last_spell_var.set(f"Last spell: {data}")
                elif event == "last_guess":
                    self.last_guess_var.set(f"AI guess: {data}")
                elif event == "motion_saved":
                    self.samples_var.set(f"Samples: {data}")
                elif event in ["training_updated", "spells_changed"]:
                    self.refresh_training_buttons()
                elif event == "toast":
                    self.append_log(str(data))
        except queue.Empty:
            pass
        self.after(100, self.process_ui_queue)

    def on_close(self):
        self.core.stop_requested = True
        try:
            self.core.run_async(self.core.disconnect())
        except Exception:
            pass
        self.destroy()


if __name__ == "__main__":
    app = MagicCasterGUI()
    app.protocol("WM_DELETE_WINDOW", app.on_close)
    app.mainloop()
