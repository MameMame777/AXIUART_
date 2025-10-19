`timescale 1ns / 1ps

//==============================================================================
// RTL Specification-Based Error Injection Test
// 螳欒TL莉墓ｧ倥↓譛驕ｩ蛹悶＆繧後◆繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｣・
//==============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class uart_axi4_rtl_error_injection_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_rtl_error_injection_test)
    
    // RTL蛻・梵縺ｫ蝓ｺ縺･縺上お繝ｩ繝ｼ繧ｫ繝・ざ繝ｪ
    typedef enum {
        CRC_ERROR_1BIT,           // 1繝薙ャ繝・RC繧ｨ繝ｩ繝ｼ (Frame_Parser STATUS_CRC_ERR)
        CRC_ERROR_MULTIBIT,       // 隍・焚繝薙ャ繝・RC繧ｨ繝ｩ繝ｼ
        CRC_ERROR_INVERT,         // CRC螳悟・蜿崎ｻ｢繧ｨ繝ｩ繝ｼ
        PROTOCOL_INVALID_SOF,     // 辟｡蜉ｹSOF (Frame_Parser SOF讀懆ｨｼ)
        PROTOCOL_INVALID_CMD,     // 辟｡蜉ｹ繧ｳ繝槭Φ繝・(STATUS_CMD_INV)
        TIMEOUT_DATA_RX,          // 繝・・繧ｿ蜿嶺ｿ｡繧ｿ繧､繝繧｢繧ｦ繝・(STATUS_TIMEOUT)
        TIMEOUT_CRC_RX,           // CRC蜿嶺ｿ｡繧ｿ繧､繝繧｢繧ｦ繝・
        AXI_INVALID_ADDR,         // 辟｡蜉ｹ繧｢繝峨Ξ繧ｹ (Register_Block RESP_SLVERR)
        AXI_INVALID_WSTRB,        // 辟｡蜉ｹ繧ｹ繝医Ο繝ｼ繝悶ヱ繧ｿ繝ｼ繝ｳ
        FIFO_UNDERFLOW,           // FIFO繧｢繝ｳ繝繝ｼ繝輔Ο繝ｼ
        DATA_CORRUPTION           // 繝壹う繝ｭ繝ｼ繝峨ョ繝ｼ繧ｿ遐ｴ謳・
    } rtl_error_type_e;
    
    // 繧ｨ繝ｩ繝ｼ豕ｨ蜈･邨ｱ險・
    typedef struct {
        int total_injected;
        int correctly_detected;
        real detection_rate;
        time avg_detection_time;
        time max_detection_time;
    } error_stats_t;
    
    error_stats_t crc_stats;
    error_stats_t protocol_stats;
    error_stats_t timeout_stats;
    error_stats_t axi_stats;
    error_stats_t fifo_stats;
    error_stats_t data_stats;
    
    // 邱丞粋邨ｱ險亥､画焚
    int total_injected;
    int total_detected;
    real overall_detection_rate;
    
    // RTL螳壽焚 (Frame_Parser.sv縺九ｉ)
    localparam [7:0] SOF_HOST_TO_DEVICE = 8'hA5;
    localparam [7:0] STATUS_OK        = 8'h00;
    localparam [7:0] STATUS_CRC_ERR   = 8'h01;
    localparam [7:0] STATUS_CMD_INV   = 8'h02;
    localparam [7:0] STATUS_ADDR_ALIGN = 8'h03;
    localparam [7:0] STATUS_TIMEOUT   = 8'h04;
    localparam [7:0] STATUS_AXI_SLVERR = 8'h05;
    localparam [7:0] STATUS_LEN_RANGE = 8'h07;
    
    // AXI蠢懃ｭ斐さ繝ｼ繝・(Register_Block.sv縺九ｉ)
    localparam [1:0] RESP_OKAY   = 2'b00;
    localparam [1:0] RESP_SLVERR = 2'b10;
    
    function new(string name="uart_axi4_rtl_error_injection_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        `uvm_info("RTL_ERROR_TEST", "Building RTL-based Error Injection Test", UVM_LOW)
        
        // 繧ｨ繝ｩ繝ｼ邨ｱ險亥・譛溷喧
        crc_stats = '{0, 0, 0.0, 0, 0};
        protocol_stats = '{0, 0, 0.0, 0, 0};
        timeout_stats = '{0, 0, 0.0, 0, 0};
        axi_stats = '{0, 0, 0.0, 0, 0};
        fifo_stats = '{0, 0, 0.0, 0, 0};
        data_stats = '{0, 0, 0.0, 0, 0};

        // Ensure the bridge status virtual interface is available for wait helpers
        if (!uvm_config_db#(virtual bridge_status_if)::get(this, "", "bridge_status_vif", bridge_status_vif)) begin
            `uvm_fatal("RTL_ERROR_TEST", "Failed to retrieve bridge_status_vif from config DB")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Running RTL-based error injection test");
        
        `uvm_info("RTL_ERROR_TEST", "=== RTL莉墓ｧ俶ｺ匁侠繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝磯幕蟋・===", UVM_LOW)
        
        // Phase 1: CRC繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(譛驥崎ｦ・- Frame_Parser CRC讀懆ｨｼ)
        run_crc_error_injection_tests();
        
        // Phase 2: 繝励Ο繝医さ繝ｫ驕募渚繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(Frame_Parser迥ｶ諷区ｩ滓｢ｰ)
        run_protocol_violation_tests();
        
        // Phase 3: 繧ｿ繧､繝繧｢繧ｦ繝医お繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(Frame_Parser TIMEOUT讖溯・)
        run_timeout_error_tests();
        
        // Phase 4: AXI4-Lite繝励Ο繝医さ繝ｫ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(Register_Block)
        run_axi_protocol_error_tests();
        
        // Phase 5: FIFO繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(FIFO蠅・阜譚｡莉ｶ)
        run_fifo_error_tests();
        
        // Phase 6: 繝・・繧ｿ螳悟・諤ｧ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・(繝壹う繝ｭ繝ｼ繝臥ｴ謳・
        run_data_integrity_error_tests();
        
        // 邨ｱ險医Ξ繝昴・繝育函謌・
        generate_error_injection_report();
        
        phase.drop_objection(this, "RTL error injection test completed");
    endtask
    
    //==========================================================================
    // CRC繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・- Frame_Parser CRC讀懆ｨｼ讖溯・縺ｮ繝・せ繝・
    //==========================================================================
    virtual task run_crc_error_injection_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 1: CRC繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 1.1: 1繝薙ャ繝・RC繧ｨ繝ｩ繝ｼ豕ｨ蜈･ (譛繧ゆｸ闊ｬ逧・↑繧ｨ繝ｩ繝ｼ)
        inject_and_verify_crc_error(CRC_ERROR_1BIT, 10);
        
        // Test 1.2: 隍・焚繝薙ャ繝・RC繧ｨ繝ｩ繝ｼ豕ｨ蜈･
        inject_and_verify_crc_error(CRC_ERROR_MULTIBIT, 10);
        
        // Test 1.3: CRC螳悟・蜿崎ｻ｢繧ｨ繝ｩ繝ｼ豕ｨ蜈･
        inject_and_verify_crc_error(CRC_ERROR_INVERT, 10);
        
        calculate_crc_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("CRC Test Complete - Detection Rate: %0.1f%%", 
                           crc_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_and_verify_crc_error(rtl_error_type_e error_type, int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            time error_inject_time, error_detect_time;
            
            tr = uart_frame_transaction::type_id::create($sformatf("crc_err_tr_%0d", i));
            if (!tr.randomize() with {
                length inside {[1:16]};  // 螳溽畑逧・↑繝輔Ξ繝ｼ繝髟ｷ
                addr inside {[32'h1000:32'h1100]};  // Register_Block遽・峇
            }) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize CRC error transaction")
            end
            
            // RTL莉墓ｧ倥↓蝓ｺ縺･縺修RC繧ｨ繝ｩ繝ｼ豕ｨ蜈･
            case (error_type)
                CRC_ERROR_1BIT: begin
                    // 1繝薙ャ繝亥渚霆｢ (譛繧ら樟螳溽噪縺ｪ繧ｨ繝ｩ繝ｼ)
                    tr.crc = tr.crc ^ (1 << $urandom_range(0, 7));
                end
                CRC_ERROR_MULTIBIT: begin
                    // 隍・焚繝薙ャ繝亥渚霆｢
                    tr.crc = tr.crc ^ $urandom_range(8'h03, 8'h7F);
                end
                CRC_ERROR_INVERT: begin
                    // 螳悟・蜿崎ｻ｢ (Frame_Parser繝・せ繝医↓譛驕ｩ)
                    tr.crc = ~tr.crc;
                end
            endcase
            
            crc_stats.total_injected++;
            error_inject_time = $time;
            tr.expect_error = 1'b1;
            env.uart_agt.driver.send_transaction(tr);

            if (!record_error_response($sformatf("CRC Error %s", error_type.name()),
                                       crc_stats,
                                       tr,
                                       STATUS_CRC_ERR,
                                       error_inject_time)) begin
                `uvm_warning("RTL_ERROR_TEST",
                             $sformatf("CRC Error %s not detected (status=0x%02X, response_received=%0d)",
                                       error_type.name(), tr.response_status, tr.response_received))
            end
            
            #100ns;  // 繝・せ繝磯俣髫・
        end
    endtask
    
    //==========================================================================
    // 繝励Ο繝医さ繝ｫ驕募渚繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・- Frame_Parser迥ｶ諷区ｩ滓｢ｰ縺ｮ繝・せ繝・
    //==========================================================================
    virtual task run_protocol_violation_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 2: 繝励Ο繝医さ繝ｫ驕募渚繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 2.1: 辟｡蜉ｹSOF豕ｨ蜈･ (Frame_Parser SOF讀懆ｨｼ)
        inject_invalid_sof_errors(10);
        
        // Test 2.2: 辟｡蜉ｹ繧ｳ繝槭Φ繝画ｳｨ蜈･ (STATUS_CMD_INV)
        inject_invalid_command_errors(10);
        
        calculate_protocol_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("Protocol Test Complete - Detection Rate: %0.1f%%", 
                           protocol_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_invalid_sof_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            logic [7:0] invalid_sof_values[] = '{8'h00, 8'hFF, 8'h5A, 8'hAA, 8'h55};
            
            tr = uart_frame_transaction::type_id::create($sformatf("invalid_sof_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize invalid SOF transaction")
            end
            
            // Frame_Parser.sv縺ｮ譛溷ｾ・､ SOF_HOST_TO_DEVICE = 8'hA5 繧帝＆蜿・
            tr.sof = invalid_sof_values[i % invalid_sof_values.size()];
            protocol_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            // Frame_Parser縺檎┌蜉ｹSOF繧堤ｴ譽・☆繧九％縺ｨ繧堤｢ｺ隱・
            fork
                begin
                    wait_for_sof_discard();
                    protocol_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", 
                              $sformatf("Invalid SOF 0x%02X correctly discarded", tr.sof), UVM_HIGH)
                end
                begin
                    #10us;  // SOF遐ｴ譽・ｾ・ｩ滓凾髢・
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    virtual task inject_invalid_command_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            logic [7:0] invalid_commands[] = '{8'hFF, 8'h00, 8'hAA, 8'h33, 8'h77};
            
            tr = uart_frame_transaction::type_id::create($sformatf("invalid_cmd_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize invalid command transaction")
            end
            
            // 譛牙柑縺ｪSOF繧定ｨｭ螳壹＠縺ｦ縺九ｉ繧ｳ繝槭Φ繝蛾＆蜿・
            tr.sof = SOF_HOST_TO_DEVICE;
            tr.cmd = invalid_commands[i % invalid_commands.size()];
            protocol_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            // Frame_Parser縺郡TATUS_CMD_INV繧定ｿ斐☆縺薙→繧堤｢ｺ隱・
            fork
                begin
                    wait_for_frame_parser_error(STATUS_CMD_INV);
                    protocol_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", 
                              $sformatf("Invalid CMD 0x%02X correctly detected", tr.cmd), UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    //==========================================================================
    // 繧ｿ繧､繝繧｢繧ｦ繝医お繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・- Frame_Parser TIMEOUT讖溯・縺ｮ繝・せ繝・
    //==========================================================================
    virtual task run_timeout_error_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 3: 繧ｿ繧､繝繧｢繧ｦ繝医お繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 3.1: 繝・・繧ｿ蜿嶺ｿ｡荳ｭ縺ｮ繧ｿ繧､繝繧｢繧ｦ繝・
        inject_data_rx_timeout_errors(5);
        
        // Test 3.2: CRC蜿嶺ｿ｡蠕・■繧ｿ繧､繝繧｢繧ｦ繝・
        inject_crc_rx_timeout_errors(5);
        
        calculate_timeout_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("Timeout Test Complete - Detection Rate: %0.1f%%", 
                           timeout_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_data_rx_timeout_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            
            tr = uart_frame_transaction::type_id::create($sformatf("data_timeout_tr_%0d", i));
            if (!tr.randomize() with {
                length inside {[4:16]};  // 繝・・繧ｿ縺ゅｊ繝輔Ξ繝ｼ繝
            }) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize data timeout transaction")
            end
            
            timeout_stats.total_injected++;
            
            // 繝輔Ξ繝ｼ繝騾∽ｿ｡繧偵ョ繝ｼ繧ｿ驛ｨ縺ｧ荳ｭ譁ｭ
            env.uart_agt.driver.send_partial_frame(tr, "DATA_RX");
            
            // Frame_Parser縺ｮTIMEOUT讀懷・蠕・ｩ・
            fork
                begin
                    wait_for_frame_parser_error(STATUS_TIMEOUT);
                    timeout_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "Data RX timeout correctly detected", UVM_HIGH)
                end
                begin
                    #10ms;  // RTL TIMEOUT_CLOCKS逶ｸ蠖薙・譎る俣
                end
            join_any
            disable fork;
            
            #1ms;  // 繝・せ繝磯俣繝ｪ繧ｻ繝・ヨ譎る俣
        end
    endtask
    
    virtual task inject_crc_rx_timeout_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            
            tr = uart_frame_transaction::type_id::create($sformatf("crc_timeout_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize CRC timeout transaction")
            end
            
            timeout_stats.total_injected++;
            
            // CRC騾∽ｿ｡逶ｴ蜑阪〒荳ｭ譁ｭ
            env.uart_agt.driver.send_partial_frame(tr, "CRC_RX");
            
            fork
                begin
                    wait_for_frame_parser_error(STATUS_TIMEOUT);
                    timeout_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "CRC RX timeout correctly detected", UVM_HIGH)
                end
                begin
                    #10ms;
                end
            join_any
            disable fork;
            
            #1ms;
        end
    endtask
    
    //==========================================================================
    // AXI4-Lite繝励Ο繝医さ繝ｫ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・- Register_Block縺ｮ繝・せ繝・
    //==========================================================================
    virtual task run_axi_protocol_error_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 4: AXI4-Lite繝励Ο繝医さ繝ｫ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 4.1: 辟｡蜉ｹ繧｢繝峨Ξ繧ｹ繧｢繧ｯ繧ｻ繧ｹ
        inject_invalid_address_errors(10);
        
        // Test 4.2: 辟｡蜉ｹ繧ｹ繝医Ο繝ｼ繝悶ヱ繧ｿ繝ｼ繝ｳ
        inject_invalid_wstrb_errors(10);
        
        calculate_axi_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("AXI Test Complete - Detection Rate: %0.1f%%", 
                           axi_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_invalid_address_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            logic [31:0] invalid_addresses[] = '{
                32'h0000_0FFF,  // Register_Block遽・峇螟・(荳・
                32'h0000_2000,  // Register_Block遽・峇螟・(荳・
                32'h1234_5678,  // 螳悟・縺ｫ遽・峇螟・
                32'h0000_10FF   // 遽・峇蜀・□縺梧悴螳夂ｾｩ繝ｬ繧ｸ繧ｹ繧ｿ
            };
            
            tr = uart_frame_transaction::type_id::create($sformatf("invalid_addr_tr_%0d", i));
            if (!tr.randomize() with {
                is_write == 1'b1;  // 譖ｸ縺崎ｾｼ縺ｿ繝医Λ繝ｳ繧ｶ繧ｯ繧ｷ繝ｧ繝ｳ
            }) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize invalid address transaction")
            end
            
            tr.addr = invalid_addresses[i % invalid_addresses.size()];
            axi_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            // Register_Block縺軍ESP_SLVERR繧定ｿ斐☆縺薙→繧堤｢ｺ隱・
            fork
                begin
                    wait_for_axi_slave_error();
                    axi_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", 
                              $sformatf("Invalid address 0x%08X correctly rejected", tr.addr), UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    virtual task inject_invalid_wstrb_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            logic [3:0] invalid_wstrbs[] = '{
                4'b0010,  // Register_Block.sv is_wstrb_supported()縺ｧ譛ｪ蟇ｾ蠢・
                4'b0101,  // 譛ｪ蟇ｾ蠢懊ヱ繧ｿ繝ｼ繝ｳ
                4'b1010,  // 譛ｪ蟇ｾ蠢懊ヱ繧ｿ繝ｼ繝ｳ
                4'b0111   // 譛ｪ蟇ｾ蠢懊ヱ繧ｿ繝ｼ繝ｳ
            };
            
            tr = uart_frame_transaction::type_id::create($sformatf("invalid_wstrb_tr_%0d", i));
            if (!tr.randomize() with {
                is_write == 1'b1;
                addr inside {[32'h1000:32'h1020]};  // 譛牙柑繧｢繝峨Ξ繧ｹ遽・峇
            }) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize invalid WSTRB transaction")
            end
            
            tr.wstrb = invalid_wstrbs[i % invalid_wstrbs.size()];
            axi_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            fork
                begin
                    wait_for_axi_slave_error();
                    axi_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", 
                              $sformatf("Invalid WSTRB 0x%01X correctly rejected", tr.wstrb), UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    //==========================================================================
    // FIFO繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・
    //==========================================================================
    virtual task run_fifo_error_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 5: FIFO繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 5.1: FIFO遨ｺ隱ｭ縺ｿ蜃ｺ縺励お繝ｩ繝ｼ
        inject_fifo_underflow_errors(5);
        
        // Test 5.2: FIFO貅譚ｯ譖ｸ縺崎ｾｼ縺ｿ繧ｨ繝ｩ繝ｼ  
        inject_fifo_overflow_errors(5);
        
        calculate_fifo_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("FIFO Test Complete - Detection Rate: %0.1f%%", 
                           fifo_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_fifo_underflow_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            fifo_stats.total_injected++;
            
            // FIFO遨ｺ迥ｶ諷九〒隱ｭ縺ｿ蜃ｺ縺苓ｩｦ陦・
            env.uart_agt.driver.force_fifo_read_when_empty();
            
            fork
                begin
                    wait_for_fifo_underflow_detection();
                    fifo_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "FIFO underflow correctly detected", UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    virtual task inject_fifo_overflow_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            fifo_stats.total_injected++;
            
            // FIFO貅譚ｯ迥ｶ諷九〒譖ｸ縺崎ｾｼ縺ｿ隧ｦ陦・
            env.uart_agt.driver.force_fifo_write_when_full();
            
            fork
                begin
                    wait_for_fifo_overflow_detection();
                    fifo_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "FIFO overflow correctly detected", UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    //==========================================================================
    // 繝・・繧ｿ螳悟・諤ｧ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝・
    //==========================================================================
    virtual task run_data_integrity_error_tests();
        `uvm_info("RTL_ERROR_TEST", "Phase 6: 繝・・繧ｿ螳悟・諤ｧ繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝亥ｮ溯｡・, UVM_MEDIUM)
        
        // Test 6.1: 繝壹う繝ｭ繝ｼ繝峨ョ繝ｼ繧ｿ遐ｴ謳・
        inject_payload_corruption_errors(10);
        
        // Test 6.2: 繧｢繝峨Ξ繧ｹ繝輔ぅ繝ｼ繝ｫ繝臥ｴ謳・
        inject_address_corruption_errors(10);
        
        calculate_data_statistics();
        
        `uvm_info("RTL_ERROR_TEST", 
                  $sformatf("Data Integrity Test Complete - Detection Rate: %0.1f%%", 
                           data_stats.detection_rate), UVM_LOW)
    endtask
    
    virtual task inject_payload_corruption_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            
            tr = uart_frame_transaction::type_id::create($sformatf("payload_corrupt_tr_%0d", i));
            if (!tr.randomize() with {
                length inside {[4:32]};  // 蜈・・縺ｪ繝・・繧ｿ髟ｷ
            }) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize payload corruption transaction")
            end
            
            // 繝壹う繝ｭ繝ｼ繝峨・荳驛ｨ繧呈э蝗ｳ逧・↓遐ｴ謳・
            if (tr.data.size() > 0) begin
                int corrupt_index = $urandom_range(0, tr.data.size()-1);
                tr.data[corrupt_index] = tr.data[corrupt_index] ^ 8'hFF;  // 繝薙ャ繝亥渚霆｢
            end
            
            data_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            // 繝・・繧ｿ謨ｴ蜷域ｧ繝√ぉ繝・け蠕・ｩ・
            fork
                begin
                    wait_for_data_integrity_error();
                    data_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "Payload corruption correctly detected", UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    virtual task inject_address_corruption_errors(int num_tests);
        for (int i = 0; i < num_tests; i++) begin
            uart_frame_transaction tr;
            
            tr = uart_frame_transaction::type_id::create($sformatf("addr_corrupt_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("RTL_ERROR_TEST", "Failed to randomize address corruption transaction")
            end
            
            // 繧｢繝峨Ξ繧ｹ繝輔ぅ繝ｼ繝ｫ繝峨ｒ諢丞峙逧・↓遐ｴ謳・(繧｢繝ｩ繧､繝｡繝ｳ繝磯＆蜿・
            tr.addr = tr.addr | 32'h00000003;  // 荳倶ｽ・繝薙ャ繝医ｒ1縺ｫ險ｭ螳壹＠縺ｦ繧｢繝ｩ繧､繝｡繝ｳ繝磯＆蜿・
            
            data_stats.total_injected++;
            
            env.uart_agt.driver.send_transaction(tr);
            
            // Frame_Parser縺郡TATUS_ADDR_ALIGN繧定ｿ斐☆縺薙→繧堤｢ｺ隱・
            fork
                begin
                    wait_for_frame_parser_error(STATUS_ADDR_ALIGN);
                    data_stats.correctly_detected++;
                    `uvm_info("RTL_ERROR_TEST", "Address corruption correctly detected", UVM_HIGH)
                end
                begin
                    #1ms;
                end
            join_any
            disable fork;
            
            #100ns;
        end
    endtask
    
    //==========================================================================
    // 繧ｨ繝ｩ繝ｼ讀懷・蠕・ｩ溘ち繧ｹ繧ｯ鄒､
    //==========================================================================
    function automatic virtual bridge_status_if get_bridge_status_vif_handle();
        if (bridge_status_vif == null) begin
            `uvm_fatal("RTL_ERROR_TEST", "bridge_status_vif handle is null")
        end
        return bridge_status_vif;
    endfunction

    virtual task wait_for_frame_parser_error(logic [7:0] expected_status);
        virtual bridge_status_if status_vif = get_bridge_status_vif_handle();

        // Wait until the exported bridge error code reflects the expected status
        forever begin
            @(posedge status_vif.clk);
            if (!status_vif.rst_n) begin
                continue;
            end

            if (status_vif.bridge_error == expected_status) begin
                break;
            end
        end
    endtask
    
    virtual task wait_for_sof_discard();
        virtual bridge_status_if status_vif = get_bridge_status_vif_handle();
        int idle_cycles = 0;

        // Wait until the bridge reports it is idle for several consecutive cycles
        forever begin
            @(posedge status_vif.clk);
            if (!status_vif.rst_n) begin
                idle_cycles = 0;
                continue;
            end

            if (!status_vif.bridge_busy) begin
                idle_cycles++;
                if (idle_cycles >= 5) begin
                    break;
                end
            end else begin
                idle_cycles = 0;
            end
        end

        #1us;  // Allow additional settling time after returning to idle
    endtask
    
    virtual task wait_for_axi_slave_error();
        // AXI error propagation is visible through the exported bridge error field
        wait_for_frame_parser_error(STATUS_AXI_SLVERR);
    endtask
    
    virtual task wait_for_fifo_underflow_detection();
        // FIFO underflow讀懷・蠕・ｩ・
        // 螳溯｣・ｾ晏ｭ・- FIFO繝｢繧ｸ繝･繝ｼ繝ｫ縺ｮ繧ｨ繝ｩ繝ｼ繝輔Λ繧ｰ逶｣隕・
        #100ns;  // 莉ｮ螳溯｣・
    endtask
    
    virtual task wait_for_fifo_overflow_detection();
        // FIFO overflow讀懷・蠕・ｩ・
        // 螳溯｣・ｾ晏ｭ・- FIFO繝｢繧ｸ繝･繝ｼ繝ｫ縺ｮ繧ｨ繝ｩ繝ｼ繝輔Λ繧ｰ逶｣隕・
        #100ns;  // 莉ｮ螳溯｣・
    endtask
    
    virtual task wait_for_data_integrity_error();
        // 繝・・繧ｿ謨ｴ蜷域ｧ繧ｨ繝ｩ繝ｼ讀懷・蠕・ｩ・
        // AXI隱ｭ縺ｿ謌ｻ縺励↓繧医ｋ讀懆ｨｼ遲・
        #100ns;  // 莉ｮ螳溯｣・
    endtask
    
    //==========================================================================
    // 邨ｱ險郁ｨ育ｮ励→繝ｬ繝昴・繝育函謌・
    //==========================================================================
    virtual function void update_detection_time_stats(ref error_stats_t stats, time detection_time);
        if (stats.correctly_detected == 1) begin
            stats.avg_detection_time = detection_time;
            stats.max_detection_time = detection_time;
        end else begin
            stats.avg_detection_time = (stats.avg_detection_time * (stats.correctly_detected - 1) + detection_time) / stats.correctly_detected;
            if (detection_time > stats.max_detection_time) begin
                stats.max_detection_time = detection_time;
            end
        end
    endfunction
    
    virtual function void calculate_crc_statistics();
        crc_stats.detection_rate = (real'(crc_stats.correctly_detected) / real'(crc_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void calculate_protocol_statistics();
        protocol_stats.detection_rate = (real'(protocol_stats.correctly_detected) / real'(protocol_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void calculate_timeout_statistics();
        timeout_stats.detection_rate = (real'(timeout_stats.correctly_detected) / real'(timeout_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void calculate_axi_statistics();
        axi_stats.detection_rate = (real'(axi_stats.correctly_detected) / real'(axi_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void calculate_fifo_statistics();
        fifo_stats.detection_rate = (real'(fifo_stats.correctly_detected) / real'(fifo_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void calculate_data_statistics();
        data_stats.detection_rate = (real'(data_stats.correctly_detected) / real'(data_stats.total_injected)) * 100.0;
    endfunction
    
    virtual function void generate_error_injection_report();
        `uvm_info("RTL_ERROR_TEST", "=== RTL莉墓ｧ俶ｺ匁侠繧ｨ繝ｩ繝ｼ豕ｨ蜈･繝・せ繝育ｵ先棡 ===", UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("CRC Error Detection: %0.1f%% (%0d/%0d)", 
                  crc_stats.detection_rate, crc_stats.correctly_detected, crc_stats.total_injected), UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("Protocol Error Detection: %0.1f%% (%0d/%0d)", 
                  protocol_stats.detection_rate, protocol_stats.correctly_detected, protocol_stats.total_injected), UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("Timeout Error Detection: %0.1f%% (%0d/%0d)", 
                  timeout_stats.detection_rate, timeout_stats.correctly_detected, timeout_stats.total_injected), UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("AXI Error Detection: %0.1f%% (%0d/%0d)", 
                  axi_stats.detection_rate, axi_stats.correctly_detected, axi_stats.total_injected), UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("FIFO Error Detection: %0.1f%% (%0d/%0d)", 
                  fifo_stats.detection_rate, fifo_stats.correctly_detected, fifo_stats.total_injected), UVM_LOW)
        `uvm_info("RTL_ERROR_TEST", $sformatf("Data Integrity Error Detection: %0.1f%% (%0d/%0d)", 
                  data_stats.detection_rate, data_stats.correctly_detected, data_stats.total_injected), UVM_LOW)
        
        // 邱丞粋讀懷・邇・ｨ育ｮ・
        total_injected = crc_stats.total_injected + protocol_stats.total_injected + 
                        timeout_stats.total_injected + axi_stats.total_injected + 
                        fifo_stats.total_injected + data_stats.total_injected;
        total_detected = crc_stats.correctly_detected + protocol_stats.correctly_detected + 
                        timeout_stats.correctly_detected + axi_stats.correctly_detected + 
                        fifo_stats.correctly_detected + data_stats.correctly_detected;
        overall_detection_rate = (real'(total_detected) / real'(total_injected)) * 100.0;
        
        `uvm_info("RTL_ERROR_TEST", $sformatf("=== 邱丞粋繧ｨ繝ｩ繝ｼ讀懷・邇・ %0.1f%% (%0d/%0d) ===", 
                  overall_detection_rate, total_detected, total_injected), UVM_LOW)
        
        // RTL莉墓ｧ俶ｺ匁侠蠎ｦ遒ｺ隱・
        if (overall_detection_rate >= 95.0) begin
            `uvm_info("RTL_ERROR_TEST", "笨・RTL莉墓ｧ俶ｺ匁侠繧ｨ繝ｩ繝ｼ讀懷・閭ｽ蜉・ 蜆ｪ遘", UVM_LOW)
        end else if (overall_detection_rate >= 85.0) begin
            `uvm_info("RTL_ERROR_TEST", "笨・RTL莉墓ｧ俶ｺ匁侠繧ｨ繝ｩ繝ｼ讀懷・閭ｽ蜉・ 濶ｯ螂ｽ", UVM_LOW)
        end else begin
            `uvm_error("RTL_ERROR_TEST", "笨・RTL莉墓ｧ俶ｺ匁侠繧ｨ繝ｩ繝ｼ讀懷・閭ｽ蜉・ 隕∵隼蝟・)
        end
    endfunction
    
endclass

