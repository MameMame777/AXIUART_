#!/usr/bin/env python3
"""
ビット変換パターン解析ツール
0x5A→0xADの変換法則を特定
"""

def analyze_bit_patterns():
    """ビット変換パターンの詳細解析"""
    print("🔍 ビット変換パターン解析")
    print("=" * 50)
    
    # 既知の変換パターン
    expected = 0x5A
    actual = 0xAD
    
    print(f"期待値: 0x{expected:02X} = {expected:08b}")
    print(f"実際値: 0x{actual:02X} = {actual:08b}")
    print(f"XOR:    0x{expected^actual:02X} = {expected^actual:08b}")
    
    print("\n🧮 変換パターンの可能性:")
    
    # 1. ビット反転
    inverted = expected ^ 0xFF
    print(f"1. 全ビット反転: 0x{inverted:02X} = {inverted:08b} {'✅' if inverted == actual else '❌'}")
    
    # 2. ビット順序反転
    def reverse_bits(value):
        result = 0
        for i in range(8):
            if value & (1 << i):
                result |= (1 << (7 - i))
        return result
    
    reversed_bits = reverse_bits(expected)
    print(f"2. ビット順序反転: 0x{reversed_bits:02X} = {reversed_bits:08b} {'✅' if reversed_bits == actual else '❌'}")
    
    # 3. 4ビットスワップ
    swapped_nibbles = ((expected & 0x0F) << 4) | ((expected & 0xF0) >> 4)
    print(f"3. 4ビットスワップ: 0x{swapped_nibbles:02X} = {swapped_nibbles:08b} {'✅' if swapped_nibbles == actual else '❌'}")
    
    # 4. 特定ビット反転
    for mask in [0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01, 0xFF, 0xF7, 0x7F]:
        xored = expected ^ mask
        if xored == actual:
            print(f"4. マスク0x{mask:02X}でXOR: 0x{xored:02X} = {xored:08b} ✅ 一致！")
    
    # 5. シフト操作
    for shift in range(1, 8):
        left_shift = ((expected << shift) | (expected >> (8 - shift))) & 0xFF
        right_shift = ((expected >> shift) | (expected << (8 - shift))) & 0xFF
        if left_shift == actual:
            print(f"5. 左ローテート{shift}: 0x{left_shift:02X} = {left_shift:08b} ✅ 一致！")
        if right_shift == actual:
            print(f"5. 右ローテート{shift}: 0x{right_shift:02X} = {right_shift:08b} ✅ 一致！")
    
    print("\n🎯 結論:")
    if expected ^ actual == 0xF7:
        print("XOR 0xF7 (11110111) による変換")
        print("これは特定のハードウェア問題を示唆:")
        print("- 7ビットが反転、bit[3]のみ保持")
        print("- UART送信ロジックまたはピン設定の問題")

def test_inverse_transformation():
    """逆変換テスト - 0xADを送信して0x5Aが受信されるかテスト"""
    print(f"\n🔄 逆変換仮説テスト")
    print("-" * 30)
    
    # 仮説：FPGAが0xADを送信すると、ホストが0x5Aを受信する
    # つまり、同じ変換が双方向で発生している
    
    test_value = 0xAD
    transformed = test_value ^ 0xF7
    print(f"仮説：FPGA送信 0x{test_value:02X} → ホスト受信 0x{transformed:02X}")
    
    if transformed == 0x5A:
        print("✅ 変換が可逆的！双方向で同じビット変換が発生")
        print("💡 解決策：Frame_Builderで事前に0xF7でXORして補正")
    else:
        print("❌ 変換は一方向のみ")

if __name__ == "__main__":
    analyze_bit_patterns()
    test_inverse_transformation()