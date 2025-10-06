#!/usr/bin/env python3
"""
書き込みコマンドのCRC検証
正しいコマンドフォーマットの確認
"""

def calculate_crc(data):
    """CRC計算関数"""
    return sum(data) & 0xFF

def verify_write_command():
    """書き込みコマンドの検証"""
    
    print("🔍 書き込みコマンドCRC検証")
    print("="*40)
    
    # テスト値: 0xAAAABBBB
    test_value = 0xAAAABBBB
    
    # 書き込みコマンド構築
    cmd = [0xA5, 0x20, 0x20, 0x10, 0x00, 0x00,
           test_value & 0xFF, (test_value >> 8) & 0xFF,
           (test_value >> 16) & 0xFF, (test_value >> 24) & 0xFF]
    
    print(f"💾 書き込み値: 0x{test_value:08X}")
    print(f"📦 コマンド (CRC前): {' '.join(f'{b:02X}' for b in cmd)}")
    
    # CRC計算
    crc = calculate_crc(cmd)
    print(f"🔢 計算CRC: 0x{crc:02X}")
    
    cmd_with_crc = cmd + [crc]
    print(f"📤 完全コマンド: {' '.join(f'{b:02X}' for b in cmd_with_crc)}")
    
    # 他のテスト値でも確認
    print(f"\n🧪 他のテスト値での検証:")
    
    test_values = [0x12345678, 0x00000000, 0xFFFFFFFF]
    
    for val in test_values:
        cmd = [0xA5, 0x20, 0x20, 0x10, 0x00, 0x00,
               val & 0xFF, (val >> 8) & 0xFF,
               (val >> 16) & 0xFF, (val >> 24) & 0xFF]
        crc = calculate_crc(cmd)
        cmd_with_crc = cmd + [crc]
        print(f"   値: 0x{val:08X} → CRC: 0x{crc:02X} → {' '.join(f'{b:02X}' for b in cmd_with_crc)}")
    
    # 読み取りコマンドとの比較
    print(f"\n📖 読み取りコマンド比較:")
    read_cmd = [0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00]
    read_crc = calculate_crc(read_cmd)
    read_cmd_with_crc = read_cmd + [read_crc]
    print(f"   読み取り: {' '.join(f'{b:02X}' for b in read_cmd_with_crc)} (CRC: 0x{read_crc:02X})")

if __name__ == "__main__":
    verify_write_command()