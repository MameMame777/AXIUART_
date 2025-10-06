#!/usr/bin/env python3
"""
読み出しプロトコル詳細分析ツール
"""

import struct

def analyze_read_protocol():
    print('🔍 読み出しプロトコル詳細分析')
    print('=' * 50)

    # 送信フレーム: A5 A0 20 10 00 00 9F (最新のログから）
    print('📤 送信フレーム: A5 A0 20 10 00 00 9F')
    cmd_frame = [0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F]

    print(f'  SOF: 0x{cmd_frame[0]:02X} (期待値: 0xA5 ✅)')
    print(f'  CMD: 0x{cmd_frame[1]:02X}')

    cmd = cmd_frame[1]
    rw_bit = (cmd >> 7) & 1
    inc_bit = (cmd >> 6) & 1  
    size_field = (cmd >> 4) & 3
    len_field = cmd & 0xF

    print(f'    RW: {rw_bit} (1=読み取り ✅)')
    print(f'    INC: {inc_bit} (0=固定アドレス)')
    print(f'    SIZE: {size_field} (2=32bit)')
    print(f'    LEN: {len_field} (0=1beat)')

    addr_bytes = cmd_frame[2:6]
    addr = struct.unpack('<I', bytes(addr_bytes))[0]
    print(f'  ADDR: 0x{addr:08X} (リトルエンディアン)')

    print(f'  CRC: 0x{cmd_frame[6]:02X}')

    print()
    print('📥 受信フレーム: AD 80 68 48 22 20 F0 FE')
    resp_frame = [0xAD, 0x80, 0x68, 0x48, 0x22, 0x20, 0xF0, 0xFE]

    print(f'  SOF: 0x{resp_frame[0]:02X} (実測: 0xAD, 仕様: 0x5A)')
    print(f'  STATUS: 0x{resp_frame[1]:02X} (実測: 0x80, 仕様: 0x00)')  
    print(f'  CMD_ECHO: 0x{resp_frame[2]:02X} (期待: 0xA0)')
    
    # 問題の核心：ADDR_ECHOが正しくない
    print(f'  ADDR_ECHO: {" ".join(f"0x{b:02X}" for b in resp_frame[3:7])}')
    addr_echo = struct.unpack('<I', bytes(resp_frame[3:7]))[0]
    print(f'  ADDR_ECHO値: 0x{addr_echo:08X}')

    print(f'  CRC: 0x{resp_frame[7]:02X}')

    print()
    print('🎯 プロトコル仕様との比較:')
    print('  ✅ フレーム長: 8バイト（成功時は7+データバイト）')
    print('  ⚠️  SOF: 実測0xAD vs 仕様0x5A')  
    print('  ⚠️  STATUS: 実測0x80 vs 仕様0x00（成功を示すが値が違う）')
    print('  ❌ ADDR_ECHO: 0xF0202248 vs 期待値0x00001020')
    
    print()
    print('🚨 重大な発見:')
    print('   プロトコル仕様では成功時のレスポンスは:')
    print('   SOF + STATUS + CMD + ADDR[4] + DATA[4] + CRC = 11バイト')
    print('   ')
    print('   しかし実際の受信は8バイトのみ!')
    print('   これは ADDR_ECHO が DATA として解釈されている可能性')
    
    print()
    print('📋 フレーム構造の推定:')
    print('   実際: SOF(1) + STATUS(1) + CMD(1) + DATA(4) + CRC(1) = 8バイト')
    print('   仕様: SOF(1) + STATUS(1) + CMD(1) + ADDR(4) + DATA(4) + CRC(1) = 11バイト')
    print('   ')
    print('   → ADDR_ECHOが省略されて、DATA直後にCRCが来ている')

if __name__ == "__main__":
    analyze_read_protocol()