# USB-UART-AXI4 Bridge Constraint File for Vivado
# Target Board: Zybo Z7-20
# Date: September 23, 2025
# Description: Production constraint file aligned with AXIUART_Top.sv RTL implementation
# Reference: RTL signals in AXIUART_Top.sv

###################################################################################
# Clock Constraints
###################################################################################

# System Clock - 125MHz input (matching RTL CLK_FREQ_HZ parameter)
# Zybo Z7-20 provides 125MHz system clock, period = 8.000ns
set_property -dict {PACKAGE_PIN K17 IOSTANDARD LVCMOS33} [get_ports clk]
create_clock -period 8.000 -name sys_clk_pin -waveform {0.000 4.000} -add [get_ports clk]

###################################################################################
# Reset Constraints
###################################################################################

# External reset input (active high, synchronous)
set_property -dict {PACKAGE_PIN K18 IOSTANDARD LVCMOS33} [get_ports rst]

###################################################################################
# UART Interface - JB Connector (Pmod USBUART)
###################################################################################
# PMOD UART 4-pin interface with hardware flow control
# Standard PMOD UART pinout (FPGA perspective):
# Pin1 (JB1): RTS_N - Request to Send (FPGA output, active low)
# Pin2 (JB2): RX - Receive Data (FPGA input from external device)
# Pin3 (JB3): TX - Transmit Data (FPGA output to external device)
# Pin4 (JB4): CTS_N - Clear to Send (FPGA input, active low)
##Pmod Header JB (Zybo Z7-20 only)


##Pmod Header JB (Zybo Z7-20 only)
#set_property -dict { PACKAGE_PIN V8    IOSTANDARD LVCMOS33     } [get_ports { jb[0] }]; #IO_L15P_T2_DQS_13 Sch=jb_p[1]
#set_property -dict { PACKAGE_PIN W8    IOSTANDARD LVCMOS33     } [get_ports { jb[1] }]; #IO_L15N_T2_DQS_13 Sch=jb_n[1]
#set_property -dict { PACKAGE_PIN U7    IOSTANDARD LVCMOS33     } [get_ports { jb[2] }]; #IO_L11P_T1_SRCC_13 Sch=jb_p[2]
#set_property -dict { PACKAGE_PIN V7    IOSTANDARD LVCMOS33     } [get_ports { jb[3] }]; #IO_L11N_T1_SRCC_13 Sch=jb_n[2]
#set_property -dict { PACKAGE_PIN Y7    IOSTANDARD LVCMOS33     } [get_ports { jb[4] }]; #IO_L13P_T2_MRCC_13 Sch=jb_p[3]
#set_property -dict { PACKAGE_PIN Y6    IOSTANDARD LVCMOS33     } [get_ports { jb[5] }]; #IO_L13N_T2_MRCC_13 Sch=jb_n[3]
#set_property -dict { PACKAGE_PIN V6    IOSTANDARD LVCMOS33     } [get_ports { jb[6] }]; #IO_L22P_T3_13 Sch=jb_p[4]
#set_property -dict { PACKAGE_PIN W6    IOSTANDARD LVCMOS33     } [get_ports { jb[7] }]; #IO_L22N_T3_13 Sch=jb_n[4]

# RTS_N - Request to Send (FPGA output, active low)
set_property -dict {PACKAGE_PIN V8 IOSTANDARD LVCMOS33} [get_ports uart_cts_n]
# UART_RX - Receive Data (FPGA input from external device)
set_property -dict {PACKAGE_PIN W8 IOSTANDARD LVCMOS33} [get_ports uart_tx]
# UART_TX - Transmit Data (FPGA output to external device)
set_property -dict {PACKAGE_PIN U7 IOSTANDARD LVCMOS33} [get_ports uart_rx]
# CTS_N - Clear to Send (FPGA input, active low)
set_property -dict {PACKAGE_PIN V7 IOSTANDARD LVCMOS33} [get_ports uart_rts_n]

###################################################################################
# System Status Outputs - LED indicators for debugging/monitoring
###################################################################################

# LED - System Heartbeat indicator
set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS33} [get_ports led]

###################################################################################
# Timing Constraints
###################################################################################

# UART Interface Timing Constraints
# UART signals are asynchronous but need proper timing relationship with system clock
set_input_delay -clock [get_clocks sys_clk_pin] -min 1.000 [get_ports {uart_rx uart_cts_n}]
set_input_delay -clock [get_clocks sys_clk_pin] -max 3.000 [get_ports {uart_rx uart_cts_n}]

set_output_delay -clock [get_clocks sys_clk_pin] -min 1.000 [get_ports {uart_tx uart_rts_n}]
set_output_delay -clock [get_clocks sys_clk_pin] -max 3.000 [get_ports {uart_tx uart_rts_n}]

# False path constraints for asynchronous UART signals
# UART RX/CTS are asynchronous and handled by synchronizers in RTL
set_false_path -from [get_ports {uart_rx uart_cts_n}] -to [get_clocks sys_clk_pin]
set_false_path -from [get_clocks sys_clk_pin] -to [get_ports {uart_tx uart_rts_n}]
# Reset signal is external and asynchronous
set_false_path -from [get_ports rst] -to [all_clocks]

# Optional: False paths for status output LEDs if implemented
set_false_path -to [get_ports {led[*]}]

###################################################################################
# Physical Constraints
###################################################################################

# Set slew rate and drive strength for UART output signals
# Slower slew rate reduces EMI for UART communication
set_property SLEW SLOW [get_ports uart_tx]
set_property SLEW SLOW [get_ports uart_rts_n]
set_property DRIVE 8 [get_ports uart_tx]
set_property DRIVE 8 [get_ports uart_rts_n]

# Optional: LED output characteristics if status LEDs are implemented
# set_property SLEW SLOW [get_ports {system_ready system_busy system_error}]
# set_property DRIVE 8 [get_ports {system_ready system_busy system_error}]

###################################################################################
# Configuration Constraints
###################################################################################

# Bitstream configuration settings for Zynq-7000 series
set_property CFGBVS VCCO [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]


###################################################################################
# Additional Timing Constraints for Performance
###################################################################################

# Internal clock domain constraints if needed for AXI interfaces
# Note: All internal logic operates on single clock domain in this design

# Maximum delay constraints for critical paths (if timing issues occur)
# set_max_delay -from [get_pins {uart_bridge_inst/state_reg[*]/C}] -to [get_pins {uart_bridge_inst/axi_*}] 10.0

# Multicycle path constraints for UART bit timing logic
# UART operates much slower than system clock, allow multiple cycles for timing closure


###################################################################################
# Implementation Directives (Optional)
###################################################################################

# Placement constraints for better timing closure
# set_property LOC SLICE_X50Y50 [get_cells {uart_bridge_inst/state_reg[*]}]

# Clock buffer placement (if manual control needed)
# set_property LOC BUFGCTRL_X0Y0 [get_cells {clk_IBUF_BUFG_inst}]

create_debug_core u_ila_0 ila
set_property ALL_PROBE_SAME_MU true [get_debug_cores u_ila_0]
set_property ALL_PROBE_SAME_MU_CNT 1 [get_debug_cores u_ila_0]
set_property C_ADV_TRIGGER false [get_debug_cores u_ila_0]
set_property C_DATA_DEPTH 4096 [get_debug_cores u_ila_0]
set_property C_EN_STRG_QUAL false [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_0]
set_property C_TRIGIN_EN false [get_debug_cores u_ila_0]
set_property C_TRIGOUT_EN false [get_debug_cores u_ila_0]
set_property port_width 1 [get_debug_ports u_ila_0/clk]
connect_debug_port u_ila_0/clk [get_nets [list clk_IBUF_BUFG]]
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe0]
set_property port_width 2 [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_state[0]} {uart_bridge_inst/uart_rx_inst/rx_state[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe1]
set_property port_width 2 [get_debug_ports u_ila_0/probe1]
connect_debug_port u_ila_0/probe1 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_sync[0]} {uart_bridge_inst/uart_rx_inst/rx_sync[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe2]
set_property port_width 4 [get_debug_ports u_ila_0/probe2]
connect_debug_port u_ila_0/probe2 [get_nets [list {uart_bridge_inst/uart_rx_inst/sample_counter[0]} {uart_bridge_inst/uart_rx_inst/sample_counter[1]} {uart_bridge_inst/uart_rx_inst/sample_counter[2]} {uart_bridge_inst/uart_rx_inst/sample_counter[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe3]
set_property port_width 4 [get_debug_ports u_ila_0/probe3]
connect_debug_port u_ila_0/probe3 [get_nets [list {uart_bridge_inst/uart_rx_inst/bit_counter[0]} {uart_bridge_inst/uart_rx_inst/bit_counter[1]} {uart_bridge_inst/uart_rx_inst/bit_counter[2]} {uart_bridge_inst/uart_rx_inst/bit_counter[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe4]
set_property port_width 7 [get_debug_ports u_ila_0/probe4]
connect_debug_port u_ila_0/probe4 [get_nets [list {uart_bridge_inst/uart_rx_inst/baud_counter[0]} {uart_bridge_inst/uart_rx_inst/baud_counter[1]} {uart_bridge_inst/uart_rx_inst/baud_counter[2]} {uart_bridge_inst/uart_rx_inst/baud_counter[3]} {uart_bridge_inst/uart_rx_inst/baud_counter[4]} {uart_bridge_inst/uart_rx_inst/baud_counter[5]} {uart_bridge_inst/uart_rx_inst/baud_counter[6]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe5]
set_property port_width 2 [get_debug_ports u_ila_0/probe5]
connect_debug_port u_ila_0/probe5 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_state_next[0]} {uart_bridge_inst/uart_rx_inst/rx_state_next[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe6]
set_property port_width 8 [get_debug_ports u_ila_0/probe6]
connect_debug_port u_ila_0/probe6 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_shift_reg[0]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[1]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[2]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[3]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[4]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[5]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[6]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe7]
set_property port_width 3 [get_debug_ports u_ila_0/probe7]
connect_debug_port u_ila_0/probe7 [get_nets [list {uart_bridge_inst/main_state_next[0]} {uart_bridge_inst/main_state_next[1]} {uart_bridge_inst/main_state_next[2]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe8]
set_property port_width 3 [get_debug_ports u_ila_0/probe8]
connect_debug_port u_ila_0/probe8 [get_nets [list {uart_bridge_inst/main_state[0]} {uart_bridge_inst/main_state[1]} {uart_bridge_inst/main_state[2]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe9]
set_property port_width 6 [get_debug_ports u_ila_0/probe9]
connect_debug_port u_ila_0/probe9 [get_nets [list {uart_bridge_inst/parser_data_count[0]} {uart_bridge_inst/parser_data_count[1]} {uart_bridge_inst/parser_data_count[2]} {uart_bridge_inst/parser_data_count[3]} {uart_bridge_inst/parser_data_count[4]} {uart_bridge_inst/parser_data_count[5]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe10]
set_property port_width 8 [get_debug_ports u_ila_0/probe10]
connect_debug_port u_ila_0/probe10 [get_nets [list {uart_bridge_inst/parser_cmd[0]} {uart_bridge_inst/parser_cmd[1]} {uart_bridge_inst/parser_cmd[2]} {uart_bridge_inst/parser_cmd[3]} {uart_bridge_inst/parser_cmd[4]} {uart_bridge_inst/parser_cmd[5]} {uart_bridge_inst/parser_cmd[6]} {uart_bridge_inst/parser_cmd[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe11]
set_property port_width 32 [get_debug_ports u_ila_0/probe11]
connect_debug_port u_ila_0/probe11 [get_nets [list {uart_bridge_inst/parser_addr[0]} {uart_bridge_inst/parser_addr[1]} {uart_bridge_inst/parser_addr[2]} {uart_bridge_inst/parser_addr[3]} {uart_bridge_inst/parser_addr[4]} {uart_bridge_inst/parser_addr[5]} {uart_bridge_inst/parser_addr[6]} {uart_bridge_inst/parser_addr[7]} {uart_bridge_inst/parser_addr[8]} {uart_bridge_inst/parser_addr[9]} {uart_bridge_inst/parser_addr[10]} {uart_bridge_inst/parser_addr[11]} {uart_bridge_inst/parser_addr[12]} {uart_bridge_inst/parser_addr[13]} {uart_bridge_inst/parser_addr[14]} {uart_bridge_inst/parser_addr[15]} {uart_bridge_inst/parser_addr[16]} {uart_bridge_inst/parser_addr[17]} {uart_bridge_inst/parser_addr[18]} {uart_bridge_inst/parser_addr[19]} {uart_bridge_inst/parser_addr[20]} {uart_bridge_inst/parser_addr[21]} {uart_bridge_inst/parser_addr[22]} {uart_bridge_inst/parser_addr[23]} {uart_bridge_inst/parser_addr[24]} {uart_bridge_inst/parser_addr[25]} {uart_bridge_inst/parser_addr[26]} {uart_bridge_inst/parser_addr[27]} {uart_bridge_inst/parser_addr[28]} {uart_bridge_inst/parser_addr[29]} {uart_bridge_inst/parser_addr[30]} {uart_bridge_inst/parser_addr[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe12]
set_property port_width 8 [get_debug_ports u_ila_0/probe12]
connect_debug_port u_ila_0/probe12 [get_nets [list {fifo_status[0]} {fifo_status[1]} {fifo_status[2]} {fifo_status[3]} {fifo_status[4]} {fifo_status[5]} {fifo_status[6]} {fifo_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe13]
set_property port_width 8 [get_debug_ports u_ila_0/probe13]
connect_debug_port u_ila_0/probe13 [get_nets [list {bridge_error_code[0]} {bridge_error_code[1]} {bridge_error_code[2]} {bridge_error_code[3]} {bridge_error_code[4]} {bridge_error_code[5]} {bridge_error_code[6]} {bridge_error_code[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe14]
set_property port_width 8 [get_debug_ports u_ila_0/probe14]
connect_debug_port u_ila_0/probe14 [get_nets [list {uart_bridge_inst/tx_fifo_data[0]} {uart_bridge_inst/tx_fifo_data[1]} {uart_bridge_inst/tx_fifo_data[2]} {uart_bridge_inst/tx_fifo_data[3]} {uart_bridge_inst/tx_fifo_data[4]} {uart_bridge_inst/tx_fifo_data[5]} {uart_bridge_inst/tx_fifo_data[6]} {uart_bridge_inst/tx_fifo_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe15]
set_property port_width 16 [get_debug_ports u_ila_0/probe15]
connect_debug_port u_ila_0/probe15 [get_nets [list {rx_count[0]} {rx_count[1]} {rx_count[2]} {rx_count[3]} {rx_count[4]} {rx_count[5]} {rx_count[6]} {rx_count[7]} {rx_count[8]} {rx_count[9]} {rx_count[10]} {rx_count[11]} {rx_count[12]} {rx_count[13]} {rx_count[14]} {rx_count[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe16]
set_property port_width 16 [get_debug_ports u_ila_0/probe16]
connect_debug_port u_ila_0/probe16 [get_nets [list {tx_count[0]} {tx_count[1]} {tx_count[2]} {tx_count[3]} {tx_count[4]} {tx_count[5]} {tx_count[6]} {tx_count[7]} {tx_count[8]} {tx_count[9]} {tx_count[10]} {tx_count[11]} {tx_count[12]} {tx_count[13]} {tx_count[14]} {tx_count[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe17]
set_property port_width 8 [get_debug_ports u_ila_0/probe17]
connect_debug_port u_ila_0/probe17 [get_nets [list {uart_bridge_inst/tx_fifo_rd_data[0]} {uart_bridge_inst/tx_fifo_rd_data[1]} {uart_bridge_inst/tx_fifo_rd_data[2]} {uart_bridge_inst/tx_fifo_rd_data[3]} {uart_bridge_inst/tx_fifo_rd_data[4]} {uart_bridge_inst/tx_fifo_rd_data[5]} {uart_bridge_inst/tx_fifo_rd_data[6]} {uart_bridge_inst/tx_fifo_rd_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe18]
set_property port_width 7 [get_debug_ports u_ila_0/probe18]
connect_debug_port u_ila_0/probe18 [get_nets [list {uart_bridge_inst/rx_fifo_count[0]} {uart_bridge_inst/rx_fifo_count[1]} {uart_bridge_inst/rx_fifo_count[2]} {uart_bridge_inst/rx_fifo_count[3]} {uart_bridge_inst/rx_fifo_count[4]} {uart_bridge_inst/rx_fifo_count[5]} {uart_bridge_inst/rx_fifo_count[6]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe19]
set_property port_width 8 [get_debug_ports u_ila_0/probe19]
connect_debug_port u_ila_0/probe19 [get_nets [list {uart_bridge_inst/parser_error_status[0]} {uart_bridge_inst/parser_error_status[1]} {uart_bridge_inst/parser_error_status[2]} {uart_bridge_inst/parser_error_status[3]} {uart_bridge_inst/parser_error_status[4]} {uart_bridge_inst/parser_error_status[5]} {uart_bridge_inst/parser_error_status[6]} {uart_bridge_inst/parser_error_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe20]
set_property port_width 16 [get_debug_ports u_ila_0/probe20]
connect_debug_port u_ila_0/probe20 [get_nets [list {uart_bridge_inst/rx_count_reg[0]} {uart_bridge_inst/rx_count_reg[1]} {uart_bridge_inst/rx_count_reg[2]} {uart_bridge_inst/rx_count_reg[3]} {uart_bridge_inst/rx_count_reg[4]} {uart_bridge_inst/rx_count_reg[5]} {uart_bridge_inst/rx_count_reg[6]} {uart_bridge_inst/rx_count_reg[7]} {uart_bridge_inst/rx_count_reg[8]} {uart_bridge_inst/rx_count_reg[9]} {uart_bridge_inst/rx_count_reg[10]} {uart_bridge_inst/rx_count_reg[11]} {uart_bridge_inst/rx_count_reg[12]} {uart_bridge_inst/rx_count_reg[13]} {uart_bridge_inst/rx_count_reg[14]} {uart_bridge_inst/rx_count_reg[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe21]
set_property port_width 8 [get_debug_ports u_ila_0/probe21]
connect_debug_port u_ila_0/probe21 [get_nets [list {uart_bridge_inst/rx_data[0]} {uart_bridge_inst/rx_data[1]} {uart_bridge_inst/rx_data[2]} {uart_bridge_inst/rx_data[3]} {uart_bridge_inst/rx_data[4]} {uart_bridge_inst/rx_data[5]} {uart_bridge_inst/rx_data[6]} {uart_bridge_inst/rx_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe22]
set_property port_width 16 [get_debug_ports u_ila_0/probe22]
connect_debug_port u_ila_0/probe22 [get_nets [list {uart_bridge_inst/tx_count_reg[0]} {uart_bridge_inst/tx_count_reg[1]} {uart_bridge_inst/tx_count_reg[2]} {uart_bridge_inst/tx_count_reg[3]} {uart_bridge_inst/tx_count_reg[4]} {uart_bridge_inst/tx_count_reg[5]} {uart_bridge_inst/tx_count_reg[6]} {uart_bridge_inst/tx_count_reg[7]} {uart_bridge_inst/tx_count_reg[8]} {uart_bridge_inst/tx_count_reg[9]} {uart_bridge_inst/tx_count_reg[10]} {uart_bridge_inst/tx_count_reg[11]} {uart_bridge_inst/tx_count_reg[12]} {uart_bridge_inst/tx_count_reg[13]} {uart_bridge_inst/tx_count_reg[14]} {uart_bridge_inst/tx_count_reg[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe23]
set_property port_width 7 [get_debug_ports u_ila_0/probe23]
connect_debug_port u_ila_0/probe23 [get_nets [list {uart_bridge_inst/tx_fifo_count[0]} {uart_bridge_inst/tx_fifo_count[1]} {uart_bridge_inst/tx_fifo_count[2]} {uart_bridge_inst/tx_fifo_count[3]} {uart_bridge_inst/tx_fifo_count[4]} {uart_bridge_inst/tx_fifo_count[5]} {uart_bridge_inst/tx_fifo_count[6]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe24]
set_property port_width 8 [get_debug_ports u_ila_0/probe24]
connect_debug_port u_ila_0/probe24 [get_nets [list {uart_bridge_inst/tx_data[0]} {uart_bridge_inst/tx_data[1]} {uart_bridge_inst/tx_data[2]} {uart_bridge_inst/tx_data[3]} {uart_bridge_inst/tx_data[4]} {uart_bridge_inst/tx_data[5]} {uart_bridge_inst/tx_data[6]} {uart_bridge_inst/tx_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe25]
set_property port_width 8 [get_debug_ports u_ila_0/probe25]
connect_debug_port u_ila_0/probe25 [get_nets [list {uart_bridge_inst/rx_fifo_rd_data[0]} {uart_bridge_inst/rx_fifo_rd_data[1]} {uart_bridge_inst/rx_fifo_rd_data[2]} {uart_bridge_inst/rx_fifo_rd_data[3]} {uart_bridge_inst/rx_fifo_rd_data[4]} {uart_bridge_inst/rx_fifo_rd_data[5]} {uart_bridge_inst/rx_fifo_rd_data[6]} {uart_bridge_inst/rx_fifo_rd_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe26]
set_property port_width 8 [get_debug_ports u_ila_0/probe26]
connect_debug_port u_ila_0/probe26 [get_nets [list {uart_bridge_inst/rx_fifo_data[0]} {uart_bridge_inst/rx_fifo_data[1]} {uart_bridge_inst/rx_fifo_data[2]} {uart_bridge_inst/rx_fifo_data[3]} {uart_bridge_inst/rx_fifo_data[4]} {uart_bridge_inst/rx_fifo_data[5]} {uart_bridge_inst/rx_fifo_data[6]} {uart_bridge_inst/rx_fifo_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe27]
set_property port_width 1 [get_debug_ports u_ila_0/probe27]
connect_debug_port u_ila_0/probe27 [get_nets [list uart_bridge_inst/uart_rx_inst/baud_tick]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe28]
set_property port_width 1 [get_debug_ports u_ila_0/probe28]
connect_debug_port u_ila_0/probe28 [get_nets [list bridge_busy]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe29]
set_property port_width 1 [get_debug_ports u_ila_0/probe29]
connect_debug_port u_ila_0/probe29 [get_nets [list bridge_enable]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe30]
set_property port_width 1 [get_debug_ports u_ila_0/probe30]
connect_debug_port u_ila_0/probe30 [get_nets [list internal_rst]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe31]
set_property port_width 1 [get_debug_ports u_ila_0/probe31]
connect_debug_port u_ila_0/probe31 [get_nets [list uart_bridge_inst/parser_busy]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe32]
set_property port_width 1 [get_debug_ports u_ila_0/probe32]
connect_debug_port u_ila_0/probe32 [get_nets [list uart_bridge_inst/parser_frame_consumed]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe33]
set_property port_width 1 [get_debug_ports u_ila_0/probe33]
connect_debug_port u_ila_0/probe33 [get_nets [list uart_bridge_inst/parser_frame_error]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe34]
set_property port_width 1 [get_debug_ports u_ila_0/probe34]
connect_debug_port u_ila_0/probe34 [get_nets [list uart_bridge_inst/parser_frame_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe35]
set_property port_width 1 [get_debug_ports u_ila_0/probe35]
connect_debug_port u_ila_0/probe35 [get_nets [list uart_bridge_inst/rx_busy]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe36]
set_property port_width 1 [get_debug_ports u_ila_0/probe36]
connect_debug_port u_ila_0/probe36 [get_nets [list uart_bridge_inst/rx_error]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe37]
set_property port_width 1 [get_debug_ports u_ila_0/probe37]
connect_debug_port u_ila_0/probe37 [get_nets [list uart_bridge_inst/rx_fifo_empty]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe38]
set_property port_width 1 [get_debug_ports u_ila_0/probe38]
connect_debug_port u_ila_0/probe38 [get_nets [list rx_fifo_full]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe39]
set_property port_width 1 [get_debug_ports u_ila_0/probe39]
connect_debug_port u_ila_0/probe39 [get_nets [list uart_bridge_inst/rx_fifo_full]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe40]
set_property port_width 1 [get_debug_ports u_ila_0/probe40]
connect_debug_port u_ila_0/probe40 [get_nets [list rx_fifo_high]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe41]
set_property port_width 1 [get_debug_ports u_ila_0/probe41]
connect_debug_port u_ila_0/probe41 [get_nets [list uart_bridge_inst/rx_fifo_rd_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe42]
set_property port_width 1 [get_debug_ports u_ila_0/probe42]
connect_debug_port u_ila_0/probe42 [get_nets [list uart_bridge_inst/rx_fifo_wr_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe43]
set_property port_width 1 [get_debug_ports u_ila_0/probe43]
connect_debug_port u_ila_0/probe43 [get_nets [list uart_bridge_inst/uart_rx_inst/rx_synced]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe44]
set_property port_width 1 [get_debug_ports u_ila_0/probe44]
connect_debug_port u_ila_0/probe44 [get_nets [list uart_bridge_inst/rx_transaction_complete]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe45]
set_property port_width 1 [get_debug_ports u_ila_0/probe45]
connect_debug_port u_ila_0/probe45 [get_nets [list uart_bridge_inst/rx_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe46]
set_property port_width 1 [get_debug_ports u_ila_0/probe46]
connect_debug_port u_ila_0/probe46 [get_nets [list uart_bridge_inst/uart_rx_inst/sample_tick]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe47]
set_property port_width 1 [get_debug_ports u_ila_0/probe47]
connect_debug_port u_ila_0/probe47 [get_nets [list uart_bridge_inst/tx_busy]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe48]
set_property port_width 1 [get_debug_ports u_ila_0/probe48]
connect_debug_port u_ila_0/probe48 [get_nets [list uart_bridge_inst/tx_done]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe49]
set_property port_width 1 [get_debug_ports u_ila_0/probe49]
connect_debug_port u_ila_0/probe49 [get_nets [list uart_bridge_inst/tx_fifo_empty]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe50]
set_property port_width 1 [get_debug_ports u_ila_0/probe50]
connect_debug_port u_ila_0/probe50 [get_nets [list uart_bridge_inst/tx_fifo_full]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe51]
set_property port_width 1 [get_debug_ports u_ila_0/probe51]
connect_debug_port u_ila_0/probe51 [get_nets [list uart_bridge_inst/tx_fifo_rd_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe52]
set_property port_width 1 [get_debug_ports u_ila_0/probe52]
connect_debug_port u_ila_0/probe52 [get_nets [list uart_bridge_inst/tx_fifo_wr_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe53]
set_property port_width 1 [get_debug_ports u_ila_0/probe53]
connect_debug_port u_ila_0/probe53 [get_nets [list tx_ready]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe54]
set_property port_width 1 [get_debug_ports u_ila_0/probe54]
connect_debug_port u_ila_0/probe54 [get_nets [list uart_bridge_inst/tx_start]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe55]
set_property port_width 1 [get_debug_ports u_ila_0/probe55]
connect_debug_port u_ila_0/probe55 [get_nets [list uart_bridge_inst/tx_transaction_complete]]
set_property C_CLK_INPUT_FREQ_HZ 300000000 [get_debug_cores dbg_hub]
set_property C_ENABLE_CLK_DIVIDER false [get_debug_cores dbg_hub]
set_property C_USER_SCAN_CHAIN 1 [get_debug_cores dbg_hub]
connect_debug_port dbg_hub/clk [get_nets clk_IBUF_BUFG]
