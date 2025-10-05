#!/usr/bin/env python3
"""
新しいビット変換パターン解析
0x5A→0xEBの変換法則を特定
"""

def analyze_new_bit_pattern():
    """新しいビット変換パターンの詳細解析"""
    print("🔍 新しいビット変換パターン解析")
    print("=" * 50)
    
    # 新しい変換パターン
    original_sof = 0x5A
    new_sof = 0xEB
    
    original_status = 0x06  # BUSY
    new_status = 0xDF
    
    print("SOF変換:")
    print(f"期待値: 0x{original_sof:02X} = {original_sof:08b}")
    print(f"実際値: 0x{new_sof:02X} = {new_sof:08b}")
    print(f"XOR:    0x{original_sof^new_sof:02X} = {original_sof^new_sof:08b}")
    
    print("\nSTATUS変換:")
    print(f"期待値: 0x{original_status:02X} = {original_status:08b}")
    print(f"実際値: 0x{new_status:02X} = {new_status:08b}")
    print(f"XOR:    0x{original_status^new_status:02X} = {original_status^new_status:08b}")
    
    print("\n🧮 変換パターンの可能性:")
    
    # 1. 共通のXORマスク確認
    sof_mask = original_sof ^ new_sof
    status_mask = original_status ^ new_status
    
    print(f"1. SOF XORマスク: 0x{sof_mask:02X} = {sof_mask:08b}")
    print(f"2. STATUS XORマスク: 0x{status_mask:02X} = {status_mask:08b}")
    
    if sof_mask == status_mask:
        print(f"✅ 共通のXORマスク: 0x{sof_mask:02X}")
        print("   すべてのデータに同じ変換が適用されている")
    else:
        print("❌ XORマスクが一致しない - より複雑な変換")
    
    # 2. 以前のパターンとの比較
    old_sof = 0xAD  # 以前のSOF異常値
    old_status = 0x80  # 以前のSTATUS異常値
    
    print(f"\n📊 以前のパターンとの比較:")
    print(f"以前のSOF: 0x5A → 0x{old_sof:02X} (XOR 0x{original_sof^old_sof:02X})")
    print(f"現在のSOF: 0x5A → 0x{new_sof:02X} (XOR 0x{sof_mask:02X})")
    
    # 3. Frame_Builder補正の効果確認
    corrected_sof = 0x5A ^ 0xF7  # Frame_Builderで適用した補正
    print(f"\n🔧 Frame_Builder補正の効果:")
    print(f"補正前送信予定: 0x5A")
    print(f"補正後実際送信: 0x{corrected_sof:02X}")
    print(f"ホスト受信値: 0x{new_sof:02X}")
    
    # 4. 新しい補正値の計算
    if sof_mask == status_mask:
        new_correction = sof_mask
        print(f"\n💡 新しい補正マスク: 0x{new_correction:02X}")
        
        # 検証
        corrected_sof_new = 0x5A ^ new_correction
        corrected_status_new = 0x06 ^ new_correction
        
        print(f"新補正でのSOF送信値: 0x{corrected_sof_new:02X}")
        print(f"新補正でのSTATUS送信値: 0x{corrected_status_new:02X}")
        
        return new_correction
    
    return None

def compare_patterns():
    """パターン変化の原因分析"""
    print(f"\n🎯 パターン変化の原因分析:")
    print("-" * 30)
    
    print("可能性1: RTL補正の副作用")
    print("  - Frame_Builderの補正が追加の変換を引き起こした")
    print("  - ハードウェアで二重変換が発生している")
    
    print("\n可能性2: FPGAビットストリームの変更")
    print("  - 新しいビットストリームで異なる変換が発生")
    print("  - ピン設定やI/O標準の変更の影響")
    
    print("\n可能性3: タイミングの問題")
    print("  - UARTタイミング変更による影響")
    print("  - ボーレート設定の変更")

if __name__ == "__main__":
    new_mask = analyze_new_bit_pattern()
    compare_patterns()
    
    if new_mask is not None:
        print(f"\n🚀 推奨アクション:")
        print(f"Frame_Builderの補正マスクを 0xF7 → 0x{new_mask:02X} に変更")