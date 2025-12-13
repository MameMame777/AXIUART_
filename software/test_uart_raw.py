#!/usr/bin/env python3
"""Quick UART diagnostic test"""
import serial
import time

port = 'COM3'
baudrate = 115200

print(f"Opening {port} at {baudrate} baud...")
s = serial.Serial(port, baudrate, timeout=1.0)
print("✓ Port opened")

# Send VERSION read command
cmd = bytes([0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xDE])
print(f"TX: {cmd.hex()}")
s.write(cmd)
s.flush()

# Wait and receive
time.sleep(0.1)
rx = s.read(100)

if rx:
    print(f"RX ({len(rx)} bytes): {rx.hex()}")
else:
    print("RX: NO RESPONSE")

s.close()
print("Port closed")
