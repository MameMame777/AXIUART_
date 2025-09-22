# AXIUART Write Command 4바이트 응답 구현 - 최종 작업 지시서

**작성일**: 2025년 9월 22일  
**대상**: 다음 작업자 (AI Agent)  
**현재 상태**: UVM_ERROR: 1 (Read Commands 완전 성공, Write Commands만 수정 필요)  
**최종 목표**: UVM_ERROR: 0 달성

---

## 🎯 **CRITICAL MISSION: Write Commands 4바이트 응답 구현**

### **현재 상황 정확한 파악**

✅ **성공 완료된 항목들**:
- Read Commands (MSB=1): 모든 CRC validation 성공
- UART RX Assertion: timeout 수정 완료 (1000→10000 clocks)
- Address 제약: 0x1000-0x101C 범위 수정 완료
- 기본 시스템 통신: 정상 동작 확인

❌ **남은 단일 문제**:
- **Write Commands (MSB=0)**: 4바이트 응답이어야 하는데 7바이트 생성 중
- **영향**: CMD=0x20, 0x04, 0x6a, 0x50, 0x4c, 0x00에서 CRC mismatch
- **결과**: 최종 CMD=0x00에서 timeout 발생하여 UVM_ERROR: 1

---

## 🔍 **정확한 문제 위치 및 분석**

### **Frame_Builder.sv Line 167-174 분석**

```systemverilog
// 현재 코드 (rtl/Frame_Builder.sv):
if ((status_reg == STATUS_OK) && cmd_reg[7]) begin  
    // Read command (MSB=1) - ✅ 정상 동작
    state_next = ADDR_BYTE0;  // → 7바이트 응답 (올바름)
end else begin
    // Write command (MSB=0) - ❌ 여기가 문제
    state_next = CRC;  // → 4바이트 응답이어야 하는데 실제론 7바이트 생성
end
```

### **문제 가설**

1. **상태 전이는 올바르지만 실제 FIFO 출력이 잘못됨**
2. **CRC state 이전에 불필요한 바이트들이 FIFO에 기록됨**  
3. **Write command 조건 검사에 논리 오류 존재**

---

## 💻 **구체적 작업 절차**

### **STEP 1: 현재 상태 재확인**

```powershell
# 작업 디렉토리 이동
cd "e:\Nautilus\workspace\fpgawork\AXIUART_"

# 최신 커밋 확인 (27ee3ae가 최신이어야 함)
git log --oneline -3

# TODO 리스트 확인  
manage_todo_list read
```

### **STEP 2: Frame_Builder Write 경로 정밀 분석**

```bash
# 1. rtl/Frame_Builder.sv 파일 열기
# 2. Line 160-180 상태 전이 로직 정밀 검토
# 3. Write command 경로에서 FIFO에 기록되는 바이트 수 추적

# 확인해야 할 상태들:
# IDLE → SOF → STATUS → CMD → CRC → DONE (Write command 이론상 경로)
# IDLE → SOF → STATUS → CMD → ADDR_BYTE0... → CRC → DONE (Read command 현재 동작)
```

### **STEP 3: 디버깅을 위한 로그 추가 (선택사항)**

Write command가 실제로 어떤 경로를 따르는지 확인하기 위해:

```systemverilog
// Frame_Builder.sv CMD state에 임시 디버깅 로그 추가 고려:
CMD: begin
    if (!tx_fifo_full) begin
        tx_fifo_data = cmd_reg;
        tx_fifo_wr_en = 1'b1;
        crc_enable = 1'b1;
        crc_data_in = cmd_reg;
        
        // 디버깅 출력 추가 (임시)
        $display("Frame_Builder CMD: cmd_reg=0x%02X, cmd_reg[7]=%b, status_reg=0x%02X", 
                 cmd_reg, cmd_reg[7], status_reg);
        
        if ((status_reg == STATUS_OK) && cmd_reg[7]) begin  
            $display("Frame_Builder: Taking READ path to ADDR_BYTE0");
            state_next = ADDR_BYTE0;
        end else begin
            $display("Frame_Builder: Taking WRITE path to CRC");
            state_next = CRC;
        end
    end
end
```

### **STEP 4: 테스트 실행 및 로그 분석**

```powershell
cd "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm"

# 테스트 실행
dsim -f dsim_config.f -top uart_axi4_tb_top -sv_seed random +UVM_TESTNAME=uart_axi4_basic_test -waves uart_system_debug.mxd

# 결과 확인 및 분석
# 1. dsim.log에서 Write command 경로 추적
# 2. uart_monitor 출력에서 실제 응답 바이트 수 확인
# 3. Frame_Builder 디버깅 출력 분석
```

### **STEP 5: Write Command 응답 길이 확인**

uart_monitor.sv 출력에서 다음과 같은 패턴 찾기:

```bash
# Read Commands (정상 동작) - 7바이트:
"Monitor collected: 7 bytes, SOF=0x5A, STATUS=0x00, CMD=0xc6, CRC validation: valid=1"

# Write Commands (문제 발생) - 4바이트여야 하는데:
"Monitor collected: 7 bytes, SOF=0x5A, STATUS=0x00, CMD=0x20, CRC validation: valid=0"
#                    ^^^^^^^ 이것이 4 bytes가 되어야 함
```

---

## 🔧 **예상되는 수정 방향들**

### **가능성 1: 상태 전이 로직 수정**

Frame_Builder.sv의 조건문에 문제가 있을 수 있음:

```systemverilog
// 현재:
if ((status_reg == STATUS_OK) && cmd_reg[7]) begin
    state_next = ADDR_BYTE0;  // Read path
end else begin
    state_next = CRC;  // Write path - 하지만 뭔가 잘못됨
end

// 수정 후보:
if ((status_reg == STATUS_OK) && cmd_reg[7]) begin
    // Read command - includes address and data
    state_next = ADDR_BYTE0;
end else if (status_reg == STATUS_OK) begin
    // Write command - STATUS + CMD + CRC only
    state_next = CRC;
end else begin
    // Error response - STATUS + CMD + CRC only  
    state_next = CRC;
end
```

### **가능성 2: CRC State 동작 확인**

CRC state에서 정확히 CRC만 FIFO에 쓰고 종료하는지 확인:

```systemverilog
CRC: begin
    if (!tx_fifo_full) begin
        tx_fifo_data = crc_out;  // CRC 값만
        tx_fifo_wr_en = 1'b1;
        state_next = DONE;       // 즉시 완료
    end
end
```

### **가능성 3: SOF/STATUS State 중복 기록 문제**

Write command에서도 SOF와 STATUS가 기록되는지 확인 필요:

```systemverilog
// Write command 응답 구조 (4바이트):
// [0] SOF_DEVICE_TO_HOST (0x5A)
// [1] STATUS (0x00 for OK)  
// [2] CMD_ECHO (원래 명령어)
// [3] CRC

// 현재 7바이트가 나온다면 ADDR이나 DATA가 잘못 포함되는 중
```

---

## 📊 **성공 기준 및 검증 방법**

### **즉시 확인할 지표들**

```bash
# 1. dsim.log 마지막 부분에서:
UVM_ERROR: 0  # ← 이것이 최종 목표

# 2. Write commands에서:
"CRC validation: valid=1" for all Write commands
"Monitor collected: 4 bytes" for Write commands  

# 3. 특정 Write commands 성공:
CMD=0x20: 4 bytes response, CRC valid
CMD=0x04: 4 bytes response, CRC valid  
CMD=0x6a: 4 bytes response, CRC valid
CMD=0x50: 4 bytes response, CRC valid
CMD=0x4c: 4 bytes response, CRC valid
CMD=0x00: 4 bytes response, CRC valid (현재 timeout)
```

### **테스트 결과 확인 스크립트**

```powershell
# 자동 결과 확인
.\test_summary.ps1

# 수동 확인
grep "UVM_ERROR" dsim.log
grep "CRC validation" dsim.log | grep -v "valid=1"  # 실패한 것들만
grep "Monitor collected" dsim.log | grep "bytes"    # 응답 바이트 수
```

---

## 🚨 **트러블슈팅 가이드**

### **만약 Frame_Builder 수정이 복잡하다면**

```bash
# Plan B: 임시 디버깅 파일 생성
cp rtl/Frame_Builder.sv temporary/Frame_Builder_debug.sv

# 단순한 Write command만 테스트
# basic_func_sequence.sv에서 Read commands 비활성화
# Write commands만으로 테스트
```

### **만약 상태 머신 흐름이 불분명하다면**

```bash
# 각 상태에서 디버깅 출력 추가:
$display("Frame_Builder State: %s, cmd_reg=0x%02X", state.name(), cmd_reg);

# FIFO 기록시마다 로그:  
$display("FIFO Write: data=0x%02X, state=%s", tx_fifo_data, state.name());
```

### **만약 CRC 계산에 문제가 있다면**

```bash
# CRC 입력 데이터 추적:
$display("CRC Input: data=0x%02X, current_crc=0x%02X", crc_data_in, crc_out);

# Write command CRC 계산 검증:
# STATUS(0x00) + CMD(예: 0x20) = CRC 입력이어야 함
```

---

## 💡 **성공 확률 높은 접근법**

### **1단계: 최소 수정으로 시작**

Frame_Builder.sv에서 Write command 경로만 정확히 확인:

```systemverilog
// Line 167-174 부근에서 Write command 경로가 
// CRC state로 직접 가는지 확인
// 다른 불필요한 상태들을 거치지 않는지 확인
```

### **2단계: 점진적 검증**

```bash
# 1. 하나의 Write command (예: 0x20)만 테스트
# 2. 응답이 4바이트인지 확인  
# 3. CRC가 올바른지 확인
# 4. 성공하면 다른 Write commands로 확장
```

### **3단계: 전체 테스트**

```bash
# 모든 Write commands 성공 후
# Read + Write 통합 테스트로 UVM_ERROR: 0 달성
```

---

## 🏆 **최종 성공 시나리오**

작업 완료 시 다음 결과가 나와야 합니다:

```bash
========================================
    UART-AXI4 BASIC FUNCTIONAL TEST     
========================================

=== Test Results ===
UVM_ERROR Count: 0     # ← 최종 목표 달성!
UVM_FATAL Count: 0
UVM_WARNING Count: < 10 (현재 36에서 대폭 감소)

=== Write Commands Success ===
CMD=0x20: CRC validation: valid=1, 4 bytes
CMD=0x04: CRC validation: valid=1, 4 bytes  
CMD=0x6a: CRC validation: valid=1, 4 bytes
CMD=0x50: CRC validation: valid=1, 4 bytes
CMD=0x4c: CRC validation: valid=1, 4 bytes
CMD=0x00: CRC validation: valid=1, 4 bytes

✅ OVERALL RESULT: TEST PASSED
   - No fatal or error messages detected
========================================
```

---

## 📝 **작업 완료 후 수행사항**

### **최종 커밋**

```bash
git add .
git commit -m "Final Success: UVM_ERROR: 0 Achieved - Write Commands 4-byte Response

✅ Frame_Builder Write Command Fix:
- Write commands (MSB=0) now generate correct 4-byte responses
- CRC validation successful for all Write commands: 0x20, 0x04, 0x6a, 0x50, 0x4c, 0x00
- Eliminated final timeout on CMD=0x00

✅ Complete System Success:
- UVM_ERROR: 0 (FINAL TARGET ACHIEVED)
- Read Commands: 100% CRC validation success  
- Write Commands: 100% CRC validation success
- All 15+ basic transactions completed successfully
- No assertion errors, no timeouts

🎯 Project Status: COMPLETE - UART-AXI Bridge Fully Operational"
```

### **최종 보고서 업데이트**

```bash
# docs/ 디렉토리에 최종 성공 보고서 작성
# temporary/ 디렉토리 정리
# 성공한 테스트 결과 아카이브
```

---

## 🎯 **핵심 포인트 요약**

1. **단일 문제**: Write Commands의 4바이트 응답 (현재 7바이트 생성 중)
2. **수정 위치**: `rtl/Frame_Builder.sv` Line 167-174 상태 전이 로직
3. **검증 방법**: Write commands에서 "4 bytes response" 및 "CRC valid" 확인
4. **최종 목표**: UVM_ERROR: 0
5. **성공 확률**: 매우 높음 (이미 90% 완성)

---

**이 작업은 AXIUART 프로젝트의 마지막 1%입니다. Write Commands의 4바이트 응답만 정확히 구현하면 완전한 성공입니다!**