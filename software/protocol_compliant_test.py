#!/usr/bin/env python3
"""
プロトコル仕様準拠テスト（改良版）
正確なプロトコル実装でFPGAの状態を診断
CRC8実装の問題を考慮した複数パターンテスト
"""

import serial
import time
import struct

def calculate_crc8_spec(data):
    """プロトコル仕様準拠CRC-8計算（polynomial: 0x07）"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x07
            else:
                crc = crc << 1
            crc &= 0xFF
    return crc

def calculate_crc8_systemverilog(data):
    """SystemVerilog実装に合わせたCRC-8計算"""
    crc = 0x00
    for byte in data:
        crc_temp = crc ^ byte
        
        # 8回のビット処理を展開（SystemVerilogと同じ）
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        crc = crc_temp
    return crc

def calculate_crc8_working(data):
    """実際に動作するCRC8計算（現在の推測値）"""
    # 複数のCRC8バリエーションを試す
    variants = {
        'spec': calculate_crc8_spec(data),
        'systemverilog': calculate_crc8_systemverilog(data),
        'no_crc': 0x00,  # CRCチェックを無効化
        'simple_xor': sum(data) & 0xFF,  # 単純なXORチェックサム
    }
    
    # とりあえずspec版を返す（後で修正が必要）
    return variants['spec']

def build_read_request(address, crc_variant='spec'):
    """プロトコル仕様準拠リードリクエスト構築（改良版）"""
    # CMD: RW=1(read), INC=0, SIZE=10(32-bit), LEN=0001(1 beat)
    # Bit pattern: 1_0_10_0001 = 0xA1
    cmd = 0xA1
    
    # アドレス（リトルエンディアン）
    addr_bytes = [
        (address >> 0) & 0xFF,
        (address >> 8) & 0xFF, 
        (address >> 16) & 0xFF,
        (address >> 24) & 0xFF
    ]
    
    # フレーム構築: SOF + CMD + ADDR
    frame_data = [0xA5, cmd] + addr_bytes
    
    # CRC計算（CMDからADDR[3]まで）- 複数バリエーション対応
    crc_data = frame_data[1:]  # SOFを除く
    
    if crc_variant == 'spec':
        crc = calculate_crc8_spec(crc_data)
    elif crc_variant == 'systemverilog':
        crc = calculate_crc8_systemverilog(crc_data)
    elif crc_variant == 'no_crc':
        crc = 0x00
    elif crc_variant == 'simple_xor':
        crc = sum(crc_data) & 0xFF
    else:
        crc = calculate_crc8_spec(crc_data)  # デフォルト
    
    frame_data.append(crc)
    return frame_data, crc

def build_write_request(address, value, crc_variant='spec'):
    """プロトコル仕様準拠ライトリクエスト構築"""
    # CMD: RW=0(write), INC=0, SIZE=10(32-bit), LEN=0001(1 beat)
    # Bit pattern: 0_0_10_0001 = 0x21
    cmd = 0x21
    
    # アドレス（リトルエンディアン）
    addr_bytes = [
        (address >> 0) & 0xFF,
        (address >> 8) & 0xFF, 
        (address >> 16) & 0xFF,
        (address >> 24) & 0xFF
    ]
    
    # データ（リトルエンディアン）
    data_bytes = [
        (value >> 0) & 0xFF,
        (value >> 8) & 0xFF,
        (value >> 16) & 0xFF,
        (value >> 24) & 0xFF
    ]
    
    # フレーム構築: SOF + CMD + ADDR + DATA
    frame_data = [0xA5, cmd] + addr_bytes + data_bytes
    
    # CRC計算（CMDからDATA[3]まで）
    crc_data = frame_data[1:]  # SOFを除く
    
    if crc_variant == 'spec':
        crc = calculate_crc8_spec(crc_data)
    elif crc_variant == 'systemverilog':
        crc = calculate_crc8_systemverilog(crc_data)
    elif crc_variant == 'no_crc':
        crc = 0x00
    elif crc_variant == 'simple_xor':
        crc = sum(crc_data) & 0xFF
    else:
        crc = calculate_crc8_spec(crc_data)  # デフォルト
    
    frame_data.append(crc)
    return frame_data, crc

def analyze_protocol_response(response_data, expected_status=0x00, show_crc_variants=True):
    """プロトコル仕様に基づく応答解析（改良版）"""
    if len(response_data) == 0:
        return "応答なし"
    
    analysis = []
    analysis.append(f"受信データ: {' '.join(f'0x{b:02X}' for b in response_data)}")
    analysis.append(f"データ長: {len(response_data)} bytes")
    
    # SOF確認
    sof = response_data[0]
    analysis.append(f"SOF: 0x{sof:02X}")
    if sof == 0x5A:
        analysis.append("  ✅ SOF正常（プロトコル準拠）")
    elif sof == 0xA5:
        analysis.append("  ⚠️  SOF=0xA5（Host→Device用）エコーバック?")
    else:
        analysis.append(f"  ❌ SOF異常（期待値: 0x5A）")
        if sof == 0xAD:
            analysis.append("  💡 0xAD - ハードウェア変換による可能性")
    
    if len(response_data) < 2:
        analysis.append("応答が短すぎます（STATUS未受信）")
        return "\n".join(analysis)
    
    # STATUS確認
    status = response_data[1]
    analysis.append(f"STATUS: 0x{status:02X}")
    
    status_names = {
        0x00: "OK",
        0x01: "CRC_ERR", 
        0x02: "CMD_INV",
        0x03: "ADDR_ALIGN",
        0x04: "TIMEOUT",
        0x05: "AXI_SLVERR",
        0x06: "BUSY",
        0x07: "LEN_RANGE",
        0x08: "PARAM"
    }
    
    if status in status_names:
        analysis.append(f"  ✅ STATUS認識: {status_names[status]}")
        
        if status == 0x00:
            # 成功レスポンスの解析
            if len(response_data) >= 12:  # SOF + STATUS + CMD + ADDR + DATA + CRC
                cmd_echo = response_data[2]
                addr_echo = response_data[3:7]
                data_bytes = response_data[7:-1]
                crc_received = response_data[-1]
                
                analysis.append(f"  CMD echo: 0x{cmd_echo:02X}")
                analysis.append(f"  ADDR echo: {' '.join(f'0x{b:02X}' for b in addr_echo)}")
                analysis.append(f"  DATA: {' '.join(f'0x{b:02X}' for b in data_bytes)}")
                
                if len(data_bytes) == 4:
                    # 32-bit値として解釈
                    value = struct.unpack('<I', bytes(data_bytes))[0]
                    analysis.append(f"  32-bit値: 0x{value:08X}")
                
                # CRC検証（複数バリエーション）
                crc_data = response_data[1:-1]  # STATUS〜DATAまで
                if show_crc_variants:
                    analysis.append(f"  CRC検証:")
                    analysis.append(f"    受信CRC: 0x{crc_received:02X}")
                    
                    crc_spec = calculate_crc8_spec(crc_data)
                    crc_sv = calculate_crc8_systemverilog(crc_data)
                    crc_xor = sum(crc_data) & 0xFF
                    
                    analysis.append(f"    仕様準拠: 0x{crc_spec:02X} {'✅' if crc_received == crc_spec else '❌'}")
                    analysis.append(f"    SystemVerilog: 0x{crc_sv:02X} {'✅' if crc_received == crc_sv else '❌'}")
                    analysis.append(f"    XORチェック: 0x{crc_xor:02X} {'✅' if crc_received == crc_xor else '❌'}")
                    
                    if crc_received == crc_spec:
                        analysis.append("  🎯 仕様準拠CRC8実装が正解")
                    elif crc_received == crc_sv:
                        analysis.append("  🎯 SystemVerilog展開型CRC8実装が正解")
                    elif crc_received == crc_xor:
                        analysis.append("  🎯 単純XORチェックサムが正解")
                    else:
                        analysis.append("  ❓ 未知のCRC計算方式")
            else:
                analysis.append("  ⚠️  成功レスポンスが短すぎます")
                
        elif status == 0x01:  # CRC_ERR
            analysis.append("  ❌ CRC不一致 - 送信フレームのCRC計算方式を変更が必要")
            
        elif status == 0x06:  # BUSY
            analysis.append("  ⚠️  デバイスBUSY - リトライが必要")
            
    else:
        analysis.append(f"  ❌ STATUS未定義 (仕様にない値)")
        if status == 0x80:
            analysis.append("  💡 0x80はレジスタマップでSTATUS_BUSYとして定義されているが、プロトコル仕様では0x06")
        elif status == 0x82:
            analysis.append("  💡 0x82は完全に未定義 - 初期化問題の可能性")
    
    return "\n".join(analysis)

def protocol_compliant_test():
    """プロトコル仕様準拠テスト（改良版）"""
    print("📋 プロトコル仕様準拠テスト（改良版）")
    print("=" * 60)
    
    # CRC8バリエーションテスト
    crc_variants = ['spec', 'systemverilog', 'no_crc', 'simple_xor']
    successful_variant = None
    
    try:
        with serial.Serial('COM3', 115200, timeout=2) as ser:
            print("✅ COM3接続成功")
            
            # まずCRC8の正しい実装を特定
            print("\n🧪 CRC8実装特定テスト")
            print("-" * 40)
            
            test_addr = 0x0000101C  # VERSION register (読み取り専用、固定値)
            
            for variant in crc_variants:
                print(f"\n🔍 CRC8バリエーション: {variant}")
                
                # リクエスト構築
                request, crc_used = build_read_request(test_addr, variant)
                print(f"送信: {' '.join(f'0x{b:02X}' for b in request)}")
                print(f"CRC: 0x{crc_used:02X} ({variant})")
                
                # バッファクリア
                ser.reset_input_buffer()
                
                # 送信
                ser.write(bytes(request))
                time.sleep(0.3)
                
                # 応答受信
                response = ser.read(50)
                
                if response:
                    response_list = list(response)
                    print(f"受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                    
                    # STATUS確認
                    if len(response_list) >= 2:
                        status = response_list[1]
                        if status == 0x00:  # SUCCESS
                            print(f"✅ CRC8実装が正解: {variant}")
                            successful_variant = variant
                            break
                        elif status == 0x01:  # CRC_ERR
                            print(f"❌ CRC不一致: {variant}")
                        else:
                            print(f"⚠️  その他のエラー (STATUS=0x{status:02X}): {variant}")
                    else:
                        print(f"❌ 応答が短すぎます: {variant}")
                else:
                    print(f"❌ 応答なし: {variant}")
                
                time.sleep(0.5)
            
            if successful_variant:
                print(f"\n🎯 正解のCRC8実装: {successful_variant}")
            else:
                print(f"\n❓ 正解のCRC8実装が特定できませんでした")
                successful_variant = 'spec'  # とりあえずデフォルト
            
            # レジスタマップテスト
            print(f"\n📋 レジスタマップテスト (CRC8: {successful_variant})")
            print("=" * 60)
            
            test_registers = [
                {"addr": 0x00001000, "name": "CONTROL", "expected": None, "rw": True},
                {"addr": 0x00001004, "name": "STATUS", "expected": None, "rw": False},
                {"addr": 0x00001008, "name": "CONFIG", "expected": 0x00000000, "rw": True},
                {"addr": 0x0000100C, "name": "DEBUG", "expected": 0x00000000, "rw": True},
                {"addr": 0x00001010, "name": "TX_COUNT", "expected": None, "rw": False},
                {"addr": 0x00001014, "name": "RX_COUNT", "expected": None, "rw": False},
                {"addr": 0x00001018, "name": "FIFO_STAT", "expected": None, "rw": False},
                {"addr": 0x0000101C, "name": "VERSION", "expected": 0x00010000, "rw": False},
            ]
            
            for i, reg in enumerate(test_registers):
                addr = reg["addr"]
                name = reg["name"]
                expected = reg["expected"]
                is_rw = reg["rw"]
                
                print(f"\n📍 テスト {i+1}: {name}レジスタ (0x{addr:08X})")
                print("-" * 40)
                
                # READ テスト
                request, crc_used = build_read_request(addr, successful_variant)
                print(f"READ送信: {' '.join(f'0x{b:02X}' for b in request)}")
                
                # バッファクリア
                ser.reset_input_buffer()
                
                # 送信
                ser.write(bytes(request))
                time.sleep(0.3)
                
                # 応答受信
                response = ser.read(50)
                
                if response:
                    response_list = list(response)
                    print(f"READ受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                    
                    print("\n🔍 READ解析:")
                    analysis = analyze_protocol_response(response_list, 0x00, show_crc_variants=(successful_variant == 'spec'))
                    print(analysis)
                    
                    # 期待値との比較
                    if expected is not None and len(response_list) >= 11:
                        data_bytes = response_list[7:11]
                        if len(data_bytes) == 4:
                            actual_value = struct.unpack('<I', bytes(data_bytes))[0]
                            if actual_value == expected:
                                print(f"✅ 期待値一致: 0x{actual_value:08X}")
                            else:
                                print(f"⚠️  期待値不一致: 実際=0x{actual_value:08X}, 期待=0x{expected:08X}")
                
                else:
                    print("❌ READ応答なし（タイムアウト）")
                
                # WRITEテスト（RWレジスタのみ）
                if is_rw:
                    test_value = 0x12345678
                    print(f"\n📝 WRITEテスト: 0x{test_value:08X}")
                    
                    write_request, write_crc = build_write_request(addr, test_value, successful_variant)
                    print(f"WRITE送信: {' '.join(f'0x{b:02X}' for b in write_request)}")
                    
                    # バッファクリア
                    ser.reset_input_buffer()
                    
                    # 送信
                    ser.write(bytes(write_request))
                    time.sleep(0.3)
                    
                    # 応答受信
                    write_response = ser.read(20)
                    
                    if write_response:
                        write_response_list = list(write_response)
                        print(f"WRITE受信: {' '.join(f'0x{b:02X}' for b in write_response_list)}")
                        
                        print("\n🔍 WRITE解析:")
                        write_analysis = analyze_protocol_response(write_response_list, 0x00, show_crc_variants=False)
                        print(write_analysis)
                    else:
                        print("❌ WRITE応答なし（タイムアウト）")
                
                time.sleep(0.5)
            
    except Exception as e:
        print(f"❌ テストエラー: {e}")
    
    print("\n" + "=" * 60)
    print("📋 プロトコル準拠テスト完了")

if __name__ == "__main__":
    protocol_compliant_test()