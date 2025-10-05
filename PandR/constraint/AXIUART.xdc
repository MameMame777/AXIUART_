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
set_property C_DATA_DEPTH 2048 [get_debug_cores u_ila_0]
set_property C_EN_STRG_QUAL false [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_0]
set_property C_TRIGIN_EN false [get_debug_cores u_ila_0]
set_property C_TRIGOUT_EN false [get_debug_cores u_ila_0]
set_property port_width 1 [get_debug_ports u_ila_0/clk]
connect_debug_port u_ila_0/clk [get_nets [list clk_IBUF_BUFG]]
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe0]
set_property port_width 8 [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 [get_nets [list {uart_bridge_inst/frame_builder/debug_cmd_echo[0]} {uart_bridge_inst/frame_builder/debug_cmd_echo[1]} {uart_bridge_inst/frame_builder/debug_cmd_echo[2]} {uart_bridge_inst/frame_builder/debug_cmd_echo[3]} {uart_bridge_inst/frame_builder/debug_cmd_echo[4]} {uart_bridge_inst/frame_builder/debug_cmd_echo[5]} {uart_bridge_inst/frame_builder/debug_cmd_echo[6]} {uart_bridge_inst/frame_builder/debug_cmd_echo[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe1]
set_property port_width 8 [get_debug_ports u_ila_0/probe1]
connect_debug_port u_ila_0/probe1 [get_nets [list {uart_bridge_inst/frame_builder/debug_cmd_echo_out[0]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[1]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[2]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[3]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[4]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[5]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[6]} {uart_bridge_inst/frame_builder/debug_cmd_echo_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe2]
set_property port_width 8 [get_debug_ports u_ila_0/probe2]
connect_debug_port u_ila_0/probe2 [get_nets [list {uart_bridge_inst/frame_builder/debug_cmd_echo_in[0]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[1]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[2]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[3]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[4]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[5]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[6]} {uart_bridge_inst/frame_builder/debug_cmd_echo_in[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe3]
set_property port_width 8 [get_debug_ports u_ila_0/probe3]
connect_debug_port u_ila_0/probe3 [get_nets [list {uart_bridge_inst/frame_builder/debug_cmd_out[0]} {uart_bridge_inst/frame_builder/debug_cmd_out[1]} {uart_bridge_inst/frame_builder/debug_cmd_out[2]} {uart_bridge_inst/frame_builder/debug_cmd_out[3]} {uart_bridge_inst/frame_builder/debug_cmd_out[4]} {uart_bridge_inst/frame_builder/debug_cmd_out[5]} {uart_bridge_inst/frame_builder/debug_cmd_out[6]} {uart_bridge_inst/frame_builder/debug_cmd_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe4]
set_property port_width 8 [get_debug_ports u_ila_0/probe4]
connect_debug_port u_ila_0/probe4 [get_nets [list {uart_bridge_inst/frame_builder/debug_crc_input[0]} {uart_bridge_inst/frame_builder/debug_crc_input[1]} {uart_bridge_inst/frame_builder/debug_crc_input[2]} {uart_bridge_inst/frame_builder/debug_crc_input[3]} {uart_bridge_inst/frame_builder/debug_crc_input[4]} {uart_bridge_inst/frame_builder/debug_crc_input[5]} {uart_bridge_inst/frame_builder/debug_crc_input[6]} {uart_bridge_inst/frame_builder/debug_crc_input[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe5]
set_property port_width 8 [get_debug_ports u_ila_0/probe5]
connect_debug_port u_ila_0/probe5 [get_nets [list {uart_bridge_inst/frame_builder/debug_crc_result[0]} {uart_bridge_inst/frame_builder/debug_crc_result[1]} {uart_bridge_inst/frame_builder/debug_crc_result[2]} {uart_bridge_inst/frame_builder/debug_crc_result[3]} {uart_bridge_inst/frame_builder/debug_crc_result[4]} {uart_bridge_inst/frame_builder/debug_crc_result[5]} {uart_bridge_inst/frame_builder/debug_crc_result[6]} {uart_bridge_inst/frame_builder/debug_crc_result[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe6]
set_property port_width 8 [get_debug_ports u_ila_0/probe6]
connect_debug_port u_ila_0/probe6 [get_nets [list {uart_bridge_inst/frame_builder/debug_sof_sent[0]} {uart_bridge_inst/frame_builder/debug_sof_sent[1]} {uart_bridge_inst/frame_builder/debug_sof_sent[2]} {uart_bridge_inst/frame_builder/debug_sof_sent[3]} {uart_bridge_inst/frame_builder/debug_sof_sent[4]} {uart_bridge_inst/frame_builder/debug_sof_sent[5]} {uart_bridge_inst/frame_builder/debug_sof_sent[6]} {uart_bridge_inst/frame_builder/debug_sof_sent[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe7]
set_property port_width 8 [get_debug_ports u_ila_0/probe7]
connect_debug_port u_ila_0/probe7 [get_nets [list {uart_bridge_inst/frame_builder/debug_status_input[0]} {uart_bridge_inst/frame_builder/debug_status_input[1]} {uart_bridge_inst/frame_builder/debug_status_input[2]} {uart_bridge_inst/frame_builder/debug_status_input[3]} {uart_bridge_inst/frame_builder/debug_status_input[4]} {uart_bridge_inst/frame_builder/debug_status_input[5]} {uart_bridge_inst/frame_builder/debug_status_input[6]} {uart_bridge_inst/frame_builder/debug_status_input[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe8]
set_property port_width 4 [get_debug_ports u_ila_0/probe8]
connect_debug_port u_ila_0/probe8 [get_nets [list {uart_bridge_inst/frame_builder/debug_frame_state[0]} {uart_bridge_inst/frame_builder/debug_frame_state[1]} {uart_bridge_inst/frame_builder/debug_frame_state[2]} {uart_bridge_inst/frame_builder/debug_frame_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe9]
set_property port_width 8 [get_debug_ports u_ila_0/probe9]
connect_debug_port u_ila_0/probe9 [get_nets [list {uart_bridge_inst/frame_builder/debug_sof_raw[0]} {uart_bridge_inst/frame_builder/debug_sof_raw[1]} {uart_bridge_inst/frame_builder/debug_sof_raw[2]} {uart_bridge_inst/frame_builder/debug_sof_raw[3]} {uart_bridge_inst/frame_builder/debug_sof_raw[4]} {uart_bridge_inst/frame_builder/debug_sof_raw[5]} {uart_bridge_inst/frame_builder/debug_sof_raw[6]} {uart_bridge_inst/frame_builder/debug_sof_raw[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe10]
set_property port_width 6 [get_debug_ports u_ila_0/probe10]
connect_debug_port u_ila_0/probe10 [get_nets [list {uart_bridge_inst/frame_builder/debug_data_count[0]} {uart_bridge_inst/frame_builder/debug_data_count[1]} {uart_bridge_inst/frame_builder/debug_data_count[2]} {uart_bridge_inst/frame_builder/debug_data_count[3]} {uart_bridge_inst/frame_builder/debug_data_count[4]} {uart_bridge_inst/frame_builder/debug_data_count[5]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe11]
set_property port_width 8 [get_debug_ports u_ila_0/probe11]
connect_debug_port u_ila_0/probe11 [get_nets [list {uart_bridge_inst/frame_builder/debug_status_output[0]} {uart_bridge_inst/frame_builder/debug_status_output[1]} {uart_bridge_inst/frame_builder/debug_status_output[2]} {uart_bridge_inst/frame_builder/debug_status_output[3]} {uart_bridge_inst/frame_builder/debug_status_output[4]} {uart_bridge_inst/frame_builder/debug_status_output[5]} {uart_bridge_inst/frame_builder/debug_status_output[6]} {uart_bridge_inst/frame_builder/debug_status_output[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe12]
set_property port_width 8 [get_debug_ports u_ila_0/probe12]
connect_debug_port u_ila_0/probe12 [get_nets [list {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[0]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[1]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[2]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[3]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[4]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[5]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[6]} {uart_bridge_inst/frame_builder/debug_tx_fifo_data_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe13]
set_property port_width 4 [get_debug_ports u_ila_0/probe13]
connect_debug_port u_ila_0/probe13 [get_nets [list {uart_bridge_inst/frame_builder/debug_state[0]} {uart_bridge_inst/frame_builder/debug_state[1]} {uart_bridge_inst/frame_builder/debug_state[2]} {uart_bridge_inst/frame_builder/debug_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe14]
set_property port_width 1 [get_debug_ports u_ila_0/probe14]
connect_debug_port u_ila_0/probe14 [get_nets [list {uart_bridge_inst/frame_builder/state[2]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe15]
set_property port_width 8 [get_debug_ports u_ila_0/probe15]
connect_debug_port u_ila_0/probe15 [get_nets [list {uart_bridge_inst/frame_parser/debug_crc_calc[0]} {uart_bridge_inst/frame_parser/debug_crc_calc[1]} {uart_bridge_inst/frame_parser/debug_crc_calc[2]} {uart_bridge_inst/frame_parser/debug_crc_calc[3]} {uart_bridge_inst/frame_parser/debug_crc_calc[4]} {uart_bridge_inst/frame_parser/debug_crc_calc[5]} {uart_bridge_inst/frame_parser/debug_crc_calc[6]} {uart_bridge_inst/frame_parser/debug_crc_calc[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe16]
set_property port_width 8 [get_debug_ports u_ila_0/probe16]
connect_debug_port u_ila_0/probe16 [get_nets [list {uart_bridge_inst/frame_parser/debug_crc_in[0]} {uart_bridge_inst/frame_parser/debug_crc_in[1]} {uart_bridge_inst/frame_parser/debug_crc_in[2]} {uart_bridge_inst/frame_parser/debug_crc_in[3]} {uart_bridge_inst/frame_parser/debug_crc_in[4]} {uart_bridge_inst/frame_parser/debug_crc_in[5]} {uart_bridge_inst/frame_parser/debug_crc_in[6]} {uart_bridge_inst/frame_parser/debug_crc_in[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe17]
set_property port_width 8 [get_debug_ports u_ila_0/probe17]
connect_debug_port u_ila_0/probe17 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[0]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[1]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[2]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[3]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[4]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[5]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[6]} {uart_bridge_inst/frame_parser/debug_rx_cmd_parsed[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe18]
set_property port_width 6 [get_debug_ports u_ila_0/probe18]
connect_debug_port u_ila_0/probe18 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[0]} {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[1]} {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[2]} {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[3]} {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[4]} {uart_bridge_inst/frame_parser/debug_rx_expected_bytes[5]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe19]
set_property port_width 2 [get_debug_ports u_ila_0/probe19]
connect_debug_port u_ila_0/probe19 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_size_field[0]} {uart_bridge_inst/frame_parser/debug_rx_size_field[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe20]
set_property port_width 8 [get_debug_ports u_ila_0/probe20]
connect_debug_port u_ila_0/probe20 [get_nets [list {uart_bridge_inst/frame_parser/debug_cmd_decoded[0]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[1]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[2]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[3]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[4]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[5]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[6]} {uart_bridge_inst/frame_parser/debug_cmd_decoded[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe21]
set_property port_width 8 [get_debug_ports u_ila_0/probe21]
connect_debug_port u_ila_0/probe21 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_sof_proc[0]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[1]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[2]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[3]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[4]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[5]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[6]} {uart_bridge_inst/frame_parser/debug_rx_sof_proc[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe22]
set_property port_width 8 [get_debug_ports u_ila_0/probe22]
connect_debug_port u_ila_0/probe22 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_sof_raw[0]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[1]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[2]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[3]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[4]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[5]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[6]} {uart_bridge_inst/frame_parser/debug_rx_sof_raw[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe23]
set_property port_width 8 [get_debug_ports u_ila_0/probe23]
connect_debug_port u_ila_0/probe23 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[0]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[1]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[2]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[3]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[4]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[5]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[6]} {uart_bridge_inst/frame_parser/debug_rx_cmd_raw[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe24]
set_property port_width 8 [get_debug_ports u_ila_0/probe24]
connect_debug_port u_ila_0/probe24 [get_nets [list {uart_bridge_inst/frame_parser/debug_status_gen[0]} {uart_bridge_inst/frame_parser/debug_status_gen[1]} {uart_bridge_inst/frame_parser/debug_status_gen[2]} {uart_bridge_inst/frame_parser/debug_status_gen[3]} {uart_bridge_inst/frame_parser/debug_status_gen[4]} {uart_bridge_inst/frame_parser/debug_status_gen[5]} {uart_bridge_inst/frame_parser/debug_status_gen[6]} {uart_bridge_inst/frame_parser/debug_status_gen[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe25]
set_property port_width 4 [get_debug_ports u_ila_0/probe25]
connect_debug_port u_ila_0/probe25 [get_nets [list {uart_bridge_inst/frame_parser/debug_rx_len_field[0]} {uart_bridge_inst/frame_parser/debug_rx_len_field[1]} {uart_bridge_inst/frame_parser/debug_rx_len_field[2]} {uart_bridge_inst/frame_parser/debug_rx_len_field[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe26]
set_property port_width 4 [get_debug_ports u_ila_0/probe26]
connect_debug_port u_ila_0/probe26 [get_nets [list {uart_bridge_inst/frame_parser/debug_state[0]} {uart_bridge_inst/frame_parser/debug_state[1]} {uart_bridge_inst/frame_parser/debug_state[2]} {uart_bridge_inst/frame_parser/debug_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe27]
set_property port_width 8 [get_debug_ports u_ila_0/probe27]
connect_debug_port u_ila_0/probe27 [get_nets [list {uart_bridge_inst/frame_parser/debug_error_cause[0]} {uart_bridge_inst/frame_parser/debug_error_cause[1]} {uart_bridge_inst/frame_parser/debug_error_cause[2]} {uart_bridge_inst/frame_parser/debug_error_cause[3]} {uart_bridge_inst/frame_parser/debug_error_cause[4]} {uart_bridge_inst/frame_parser/debug_error_cause[5]} {uart_bridge_inst/frame_parser/debug_error_cause[6]} {uart_bridge_inst/frame_parser/debug_error_cause[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe28]
set_property port_width 8 [get_debug_ports u_ila_0/probe28]
connect_debug_port u_ila_0/probe28 [get_nets [list {uart_bridge_inst/frame_parser/debug_status_out[0]} {uart_bridge_inst/frame_parser/debug_status_out[1]} {uart_bridge_inst/frame_parser/debug_status_out[2]} {uart_bridge_inst/frame_parser/debug_status_out[3]} {uart_bridge_inst/frame_parser/debug_status_out[4]} {uart_bridge_inst/frame_parser/debug_status_out[5]} {uart_bridge_inst/frame_parser/debug_status_out[6]} {uart_bridge_inst/frame_parser/debug_status_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe29]
set_property port_width 8 [get_debug_ports u_ila_0/probe29]
connect_debug_port u_ila_0/probe29 [get_nets [list {uart_bridge_inst/frame_parser/debug_error_cause_internal[0]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[1]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[2]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[3]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[4]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[5]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[6]} {uart_bridge_inst/frame_parser/debug_error_cause_internal[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe30]
set_property port_width 4 [get_debug_ports u_ila_0/probe30]
connect_debug_port u_ila_0/probe30 [get_nets [list {uart_bridge_inst/uart_rx_inst/sample_counter[0]} {uart_bridge_inst/uart_rx_inst/sample_counter[1]} {uart_bridge_inst/uart_rx_inst/sample_counter[2]} {uart_bridge_inst/uart_rx_inst/sample_counter[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe31]
set_property port_width 7 [get_debug_ports u_ila_0/probe31]
connect_debug_port u_ila_0/probe31 [get_nets [list {uart_bridge_inst/uart_rx_inst/baud_counter[0]} {uart_bridge_inst/uart_rx_inst/baud_counter[1]} {uart_bridge_inst/uart_rx_inst/baud_counter[2]} {uart_bridge_inst/uart_rx_inst/baud_counter[3]} {uart_bridge_inst/uart_rx_inst/baud_counter[4]} {uart_bridge_inst/uart_rx_inst/baud_counter[5]} {uart_bridge_inst/uart_rx_inst/baud_counter[6]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe32]
set_property port_width 4 [get_debug_ports u_ila_0/probe32]
connect_debug_port u_ila_0/probe32 [get_nets [list {uart_bridge_inst/uart_rx_inst/bit_counter[0]} {uart_bridge_inst/uart_rx_inst/bit_counter[1]} {uart_bridge_inst/uart_rx_inst/bit_counter[2]} {uart_bridge_inst/uart_rx_inst/bit_counter[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe33]
set_property port_width 3 [get_debug_ports u_ila_0/probe33]
connect_debug_port u_ila_0/probe33 [get_nets [list {uart_bridge_inst/uart_tx_inst/debug_uart_tx_state[0]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_state[1]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_state[2]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe34]
set_property port_width 2 [get_debug_ports u_ila_0/probe34]
connect_debug_port u_ila_0/probe34 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_sync[0]} {uart_bridge_inst/uart_rx_inst/rx_sync[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe35]
set_property port_width 8 [get_debug_ports u_ila_0/probe35]
connect_debug_port u_ila_0/probe35 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_shift_reg[0]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[1]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[2]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[3]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[4]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[5]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[6]} {uart_bridge_inst/uart_rx_inst/rx_shift_reg[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe36]
set_property port_width 4 [get_debug_ports u_ila_0/probe36]
connect_debug_port u_ila_0/probe36 [get_nets [list {uart_bridge_inst/uart_tx_inst/debug_uart_bit_counter[0]} {uart_bridge_inst/uart_tx_inst/debug_uart_bit_counter[1]} {uart_bridge_inst/uart_tx_inst/debug_uart_bit_counter[2]} {uart_bridge_inst/uart_tx_inst/debug_uart_bit_counter[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe37]
set_property port_width 2 [get_debug_ports u_ila_0/probe37]
connect_debug_port u_ila_0/probe37 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_state_next[0]} {uart_bridge_inst/uart_rx_inst/rx_state_next[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe38]
set_property port_width 8 [get_debug_ports u_ila_0/probe38]
connect_debug_port u_ila_0/probe38 [get_nets [list {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[0]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[1]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[2]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[3]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[4]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[5]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[6]} {uart_bridge_inst/uart_tx_inst/debug_uart_tx_shift_reg[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe39]
set_property port_width 2 [get_debug_ports u_ila_0/probe39]
connect_debug_port u_ila_0/probe39 [get_nets [list {uart_bridge_inst/uart_rx_inst/rx_state[0]} {uart_bridge_inst/uart_rx_inst/rx_state[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe40]
set_property port_width 8 [get_debug_ports u_ila_0/probe40]
connect_debug_port u_ila_0/probe40 [get_nets [list {uart_bridge_inst/debug_uart_tx_data[0]} {uart_bridge_inst/debug_uart_tx_data[1]} {uart_bridge_inst/debug_uart_tx_data[2]} {uart_bridge_inst/debug_uart_tx_data[3]} {uart_bridge_inst/debug_uart_tx_data[4]} {uart_bridge_inst/debug_uart_tx_data[5]} {uart_bridge_inst/debug_uart_tx_data[6]} {uart_bridge_inst/debug_uart_tx_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe41]
set_property port_width 8 [get_debug_ports u_ila_0/probe41]
connect_debug_port u_ila_0/probe41 [get_nets [list {uart_bridge_inst/debug_captured_cmd[0]} {uart_bridge_inst/debug_captured_cmd[1]} {uart_bridge_inst/debug_captured_cmd[2]} {uart_bridge_inst/debug_captured_cmd[3]} {uart_bridge_inst/debug_captured_cmd[4]} {uart_bridge_inst/debug_captured_cmd[5]} {uart_bridge_inst/debug_captured_cmd[6]} {uart_bridge_inst/debug_captured_cmd[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe42]
set_property port_width 8 [get_debug_ports u_ila_0/probe42]
connect_debug_port u_ila_0/probe42 [get_nets [list {uart_bridge_inst/debug_axi_status_out[0]} {uart_bridge_inst/debug_axi_status_out[1]} {uart_bridge_inst/debug_axi_status_out[2]} {uart_bridge_inst/debug_axi_status_out[3]} {uart_bridge_inst/debug_axi_status_out[4]} {uart_bridge_inst/debug_axi_status_out[5]} {uart_bridge_inst/debug_axi_status_out[6]} {uart_bridge_inst/debug_axi_status_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe43]
set_property port_width 32 [get_debug_ports u_ila_0/probe43]
connect_debug_port u_ila_0/probe43 [get_nets [list {uart_bridge_inst/debug_axi_araddr[0]} {uart_bridge_inst/debug_axi_araddr[1]} {uart_bridge_inst/debug_axi_araddr[2]} {uart_bridge_inst/debug_axi_araddr[3]} {uart_bridge_inst/debug_axi_araddr[4]} {uart_bridge_inst/debug_axi_araddr[5]} {uart_bridge_inst/debug_axi_araddr[6]} {uart_bridge_inst/debug_axi_araddr[7]} {uart_bridge_inst/debug_axi_araddr[8]} {uart_bridge_inst/debug_axi_araddr[9]} {uart_bridge_inst/debug_axi_araddr[10]} {uart_bridge_inst/debug_axi_araddr[11]} {uart_bridge_inst/debug_axi_araddr[12]} {uart_bridge_inst/debug_axi_araddr[13]} {uart_bridge_inst/debug_axi_araddr[14]} {uart_bridge_inst/debug_axi_araddr[15]} {uart_bridge_inst/debug_axi_araddr[16]} {uart_bridge_inst/debug_axi_araddr[17]} {uart_bridge_inst/debug_axi_araddr[18]} {uart_bridge_inst/debug_axi_araddr[19]} {uart_bridge_inst/debug_axi_araddr[20]} {uart_bridge_inst/debug_axi_araddr[21]} {uart_bridge_inst/debug_axi_araddr[22]} {uart_bridge_inst/debug_axi_araddr[23]} {uart_bridge_inst/debug_axi_araddr[24]} {uart_bridge_inst/debug_axi_araddr[25]} {uart_bridge_inst/debug_axi_araddr[26]} {uart_bridge_inst/debug_axi_araddr[27]} {uart_bridge_inst/debug_axi_araddr[28]} {uart_bridge_inst/debug_axi_araddr[29]} {uart_bridge_inst/debug_axi_araddr[30]} {uart_bridge_inst/debug_axi_araddr[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe44]
set_property port_width 2 [get_debug_ports u_ila_0/probe44]
connect_debug_port u_ila_0/probe44 [get_nets [list {uart_bridge_inst/debug_axi_bresp[0]} {uart_bridge_inst/debug_axi_bresp[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe45]
set_property port_width 4 [get_debug_ports u_ila_0/probe45]
connect_debug_port u_ila_0/probe45 [get_nets [list {uart_bridge_inst/debug_bridge_state[0]} {uart_bridge_inst/debug_bridge_state[1]} {uart_bridge_inst/debug_bridge_state[2]} {uart_bridge_inst/debug_bridge_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe46]
set_property port_width 8 [get_debug_ports u_ila_0/probe46]
connect_debug_port u_ila_0/probe46 [get_nets [list {uart_bridge_inst/debug_bridge_status[0]} {uart_bridge_inst/debug_bridge_status[1]} {uart_bridge_inst/debug_bridge_status[2]} {uart_bridge_inst/debug_bridge_status[3]} {uart_bridge_inst/debug_bridge_status[4]} {uart_bridge_inst/debug_bridge_status[5]} {uart_bridge_inst/debug_bridge_status[6]} {uart_bridge_inst/debug_bridge_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe47]
set_property port_width 8 [get_debug_ports u_ila_0/probe47]
connect_debug_port u_ila_0/probe47 [get_nets [list {uart_bridge_inst/debug_builder_cmd_out[0]} {uart_bridge_inst/debug_builder_cmd_out[1]} {uart_bridge_inst/debug_builder_cmd_out[2]} {uart_bridge_inst/debug_builder_cmd_out[3]} {uart_bridge_inst/debug_builder_cmd_out[4]} {uart_bridge_inst/debug_builder_cmd_out[5]} {uart_bridge_inst/debug_builder_cmd_out[6]} {uart_bridge_inst/debug_builder_cmd_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe48]
set_property port_width 8 [get_debug_ports u_ila_0/probe48]
connect_debug_port u_ila_0/probe48 [get_nets [list {uart_bridge_inst/debug_builder_status[0]} {uart_bridge_inst/debug_builder_status[1]} {uart_bridge_inst/debug_builder_status[2]} {uart_bridge_inst/debug_builder_status[3]} {uart_bridge_inst/debug_builder_status[4]} {uart_bridge_inst/debug_builder_status[5]} {uart_bridge_inst/debug_builder_status[6]} {uart_bridge_inst/debug_builder_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe49]
set_property port_width 2 [get_debug_ports u_ila_0/probe49]
connect_debug_port u_ila_0/probe49 [get_nets [list {uart_bridge_inst/debug_axi_rresp[0]} {uart_bridge_inst/debug_axi_rresp[1]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe50]
set_property port_width 8 [get_debug_ports u_ila_0/probe50]
connect_debug_port u_ila_0/probe50 [get_nets [list {uart_bridge_inst/debug_builder_cmd_echo[0]} {uart_bridge_inst/debug_builder_cmd_echo[1]} {uart_bridge_inst/debug_builder_cmd_echo[2]} {uart_bridge_inst/debug_builder_cmd_echo[3]} {uart_bridge_inst/debug_builder_cmd_echo[4]} {uart_bridge_inst/debug_builder_cmd_echo[5]} {uart_bridge_inst/debug_builder_cmd_echo[6]} {uart_bridge_inst/debug_builder_cmd_echo[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe51]
set_property port_width 4 [get_debug_ports u_ila_0/probe51]
connect_debug_port u_ila_0/probe51 [get_nets [list {uart_bridge_inst/debug_builder_state[0]} {uart_bridge_inst/debug_builder_state[1]} {uart_bridge_inst/debug_builder_state[2]} {uart_bridge_inst/debug_builder_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe52]
set_property port_width 8 [get_debug_ports u_ila_0/probe52]
connect_debug_port u_ila_0/probe52 [get_nets [list {uart_bridge_inst/debug_parser_cmd[0]} {uart_bridge_inst/debug_parser_cmd[1]} {uart_bridge_inst/debug_parser_cmd[2]} {uart_bridge_inst/debug_parser_cmd[3]} {uart_bridge_inst/debug_parser_cmd[4]} {uart_bridge_inst/debug_parser_cmd[5]} {uart_bridge_inst/debug_parser_cmd[6]} {uart_bridge_inst/debug_parser_cmd[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe53]
set_property port_width 8 [get_debug_ports u_ila_0/probe53]
connect_debug_port u_ila_0/probe53 [get_nets [list {uart_bridge_inst/debug_parser_cmd_out[0]} {uart_bridge_inst/debug_parser_cmd_out[1]} {uart_bridge_inst/debug_parser_cmd_out[2]} {uart_bridge_inst/debug_parser_cmd_out[3]} {uart_bridge_inst/debug_parser_cmd_out[4]} {uart_bridge_inst/debug_parser_cmd_out[5]} {uart_bridge_inst/debug_parser_cmd_out[6]} {uart_bridge_inst/debug_parser_cmd_out[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe54]
set_property port_width 8 [get_debug_ports u_ila_0/probe54]
connect_debug_port u_ila_0/probe54 [get_nets [list {uart_bridge_inst/debug_parser_status[0]} {uart_bridge_inst/debug_parser_status[1]} {uart_bridge_inst/debug_parser_status[2]} {uart_bridge_inst/debug_parser_status[3]} {uart_bridge_inst/debug_parser_status[4]} {uart_bridge_inst/debug_parser_status[5]} {uart_bridge_inst/debug_parser_status[6]} {uart_bridge_inst/debug_parser_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe55]
set_property port_width 4 [get_debug_ports u_ila_0/probe55]
connect_debug_port u_ila_0/probe55 [get_nets [list {uart_bridge_inst/debug_parser_state[0]} {uart_bridge_inst/debug_parser_state[1]} {uart_bridge_inst/debug_parser_state[2]} {uart_bridge_inst/debug_parser_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe56]
set_property port_width 32 [get_debug_ports u_ila_0/probe56]
connect_debug_port u_ila_0/probe56 [get_nets [list {uart_bridge_inst/debug_axi_wdata[0]} {uart_bridge_inst/debug_axi_wdata[1]} {uart_bridge_inst/debug_axi_wdata[2]} {uart_bridge_inst/debug_axi_wdata[3]} {uart_bridge_inst/debug_axi_wdata[4]} {uart_bridge_inst/debug_axi_wdata[5]} {uart_bridge_inst/debug_axi_wdata[6]} {uart_bridge_inst/debug_axi_wdata[7]} {uart_bridge_inst/debug_axi_wdata[8]} {uart_bridge_inst/debug_axi_wdata[9]} {uart_bridge_inst/debug_axi_wdata[10]} {uart_bridge_inst/debug_axi_wdata[11]} {uart_bridge_inst/debug_axi_wdata[12]} {uart_bridge_inst/debug_axi_wdata[13]} {uart_bridge_inst/debug_axi_wdata[14]} {uart_bridge_inst/debug_axi_wdata[15]} {uart_bridge_inst/debug_axi_wdata[16]} {uart_bridge_inst/debug_axi_wdata[17]} {uart_bridge_inst/debug_axi_wdata[18]} {uart_bridge_inst/debug_axi_wdata[19]} {uart_bridge_inst/debug_axi_wdata[20]} {uart_bridge_inst/debug_axi_wdata[21]} {uart_bridge_inst/debug_axi_wdata[22]} {uart_bridge_inst/debug_axi_wdata[23]} {uart_bridge_inst/debug_axi_wdata[24]} {uart_bridge_inst/debug_axi_wdata[25]} {uart_bridge_inst/debug_axi_wdata[26]} {uart_bridge_inst/debug_axi_wdata[27]} {uart_bridge_inst/debug_axi_wdata[28]} {uart_bridge_inst/debug_axi_wdata[29]} {uart_bridge_inst/debug_axi_wdata[30]} {uart_bridge_inst/debug_axi_wdata[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe57]
set_property port_width 32 [get_debug_ports u_ila_0/probe57]
connect_debug_port u_ila_0/probe57 [get_nets [list {uart_bridge_inst/debug_axi_awaddr[0]} {uart_bridge_inst/debug_axi_awaddr[1]} {uart_bridge_inst/debug_axi_awaddr[2]} {uart_bridge_inst/debug_axi_awaddr[3]} {uart_bridge_inst/debug_axi_awaddr[4]} {uart_bridge_inst/debug_axi_awaddr[5]} {uart_bridge_inst/debug_axi_awaddr[6]} {uart_bridge_inst/debug_axi_awaddr[7]} {uart_bridge_inst/debug_axi_awaddr[8]} {uart_bridge_inst/debug_axi_awaddr[9]} {uart_bridge_inst/debug_axi_awaddr[10]} {uart_bridge_inst/debug_axi_awaddr[11]} {uart_bridge_inst/debug_axi_awaddr[12]} {uart_bridge_inst/debug_axi_awaddr[13]} {uart_bridge_inst/debug_axi_awaddr[14]} {uart_bridge_inst/debug_axi_awaddr[15]} {uart_bridge_inst/debug_axi_awaddr[16]} {uart_bridge_inst/debug_axi_awaddr[17]} {uart_bridge_inst/debug_axi_awaddr[18]} {uart_bridge_inst/debug_axi_awaddr[19]} {uart_bridge_inst/debug_axi_awaddr[20]} {uart_bridge_inst/debug_axi_awaddr[21]} {uart_bridge_inst/debug_axi_awaddr[22]} {uart_bridge_inst/debug_axi_awaddr[23]} {uart_bridge_inst/debug_axi_awaddr[24]} {uart_bridge_inst/debug_axi_awaddr[25]} {uart_bridge_inst/debug_axi_awaddr[26]} {uart_bridge_inst/debug_axi_awaddr[27]} {uart_bridge_inst/debug_axi_awaddr[28]} {uart_bridge_inst/debug_axi_awaddr[29]} {uart_bridge_inst/debug_axi_awaddr[30]} {uart_bridge_inst/debug_axi_awaddr[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe58]
set_property port_width 4 [get_debug_ports u_ila_0/probe58]
connect_debug_port u_ila_0/probe58 [get_nets [list {uart_bridge_inst/debug_axi_state[0]} {uart_bridge_inst/debug_axi_state[1]} {uart_bridge_inst/debug_axi_state[2]} {uart_bridge_inst/debug_axi_state[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe59]
set_property port_width 32 [get_debug_ports u_ila_0/probe59]
connect_debug_port u_ila_0/probe59 [get_nets [list {uart_bridge_inst/debug_captured_addr[0]} {uart_bridge_inst/debug_captured_addr[1]} {uart_bridge_inst/debug_captured_addr[2]} {uart_bridge_inst/debug_captured_addr[3]} {uart_bridge_inst/debug_captured_addr[4]} {uart_bridge_inst/debug_captured_addr[5]} {uart_bridge_inst/debug_captured_addr[6]} {uart_bridge_inst/debug_captured_addr[7]} {uart_bridge_inst/debug_captured_addr[8]} {uart_bridge_inst/debug_captured_addr[9]} {uart_bridge_inst/debug_captured_addr[10]} {uart_bridge_inst/debug_captured_addr[11]} {uart_bridge_inst/debug_captured_addr[12]} {uart_bridge_inst/debug_captured_addr[13]} {uart_bridge_inst/debug_captured_addr[14]} {uart_bridge_inst/debug_captured_addr[15]} {uart_bridge_inst/debug_captured_addr[16]} {uart_bridge_inst/debug_captured_addr[17]} {uart_bridge_inst/debug_captured_addr[18]} {uart_bridge_inst/debug_captured_addr[19]} {uart_bridge_inst/debug_captured_addr[20]} {uart_bridge_inst/debug_captured_addr[21]} {uart_bridge_inst/debug_captured_addr[22]} {uart_bridge_inst/debug_captured_addr[23]} {uart_bridge_inst/debug_captured_addr[24]} {uart_bridge_inst/debug_captured_addr[25]} {uart_bridge_inst/debug_captured_addr[26]} {uart_bridge_inst/debug_captured_addr[27]} {uart_bridge_inst/debug_captured_addr[28]} {uart_bridge_inst/debug_captured_addr[29]} {uart_bridge_inst/debug_captured_addr[30]} {uart_bridge_inst/debug_captured_addr[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe60]
set_property port_width 8 [get_debug_ports u_ila_0/probe60]
connect_debug_port u_ila_0/probe60 [get_nets [list {uart_bridge_inst/debug_uart_rx_data[0]} {uart_bridge_inst/debug_uart_rx_data[1]} {uart_bridge_inst/debug_uart_rx_data[2]} {uart_bridge_inst/debug_uart_rx_data[3]} {uart_bridge_inst/debug_uart_rx_data[4]} {uart_bridge_inst/debug_uart_rx_data[5]} {uart_bridge_inst/debug_uart_rx_data[6]} {uart_bridge_inst/debug_uart_rx_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe61]
set_property port_width 8 [get_debug_ports u_ila_0/probe61]
connect_debug_port u_ila_0/probe61 [get_nets [list {uart_bridge_inst/tx_fifo_data[0]} {uart_bridge_inst/tx_fifo_data[1]} {uart_bridge_inst/tx_fifo_data[2]} {uart_bridge_inst/tx_fifo_data[3]} {uart_bridge_inst/tx_fifo_data[4]} {uart_bridge_inst/tx_fifo_data[5]} {uart_bridge_inst/tx_fifo_data[6]} {uart_bridge_inst/tx_fifo_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe62]
set_property port_width 8 [get_debug_ports u_ila_0/probe62]
connect_debug_port u_ila_0/probe62 [get_nets [list {uart_bridge_inst/tx_fifo_rd_data[0]} {uart_bridge_inst/tx_fifo_rd_data[1]} {uart_bridge_inst/tx_fifo_rd_data[2]} {uart_bridge_inst/tx_fifo_rd_data[3]} {uart_bridge_inst/tx_fifo_rd_data[4]} {uart_bridge_inst/tx_fifo_rd_data[5]} {uart_bridge_inst/tx_fifo_rd_data[6]} {uart_bridge_inst/tx_fifo_rd_data[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe63]
set_property port_width 8 [get_debug_ports u_ila_0/probe63]
connect_debug_port u_ila_0/probe63 [get_nets [list {bridge_error_code[0]} {bridge_error_code[1]} {bridge_error_code[2]} {bridge_error_code[3]} {bridge_error_code[4]} {bridge_error_code[5]} {bridge_error_code[6]} {bridge_error_code[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe64]
set_property port_width 16 [get_debug_ports u_ila_0/probe64]
connect_debug_port u_ila_0/probe64 [get_nets [list {tx_count[0]} {tx_count[1]} {tx_count[2]} {tx_count[3]} {tx_count[4]} {tx_count[5]} {tx_count[6]} {tx_count[7]} {tx_count[8]} {tx_count[9]} {tx_count[10]} {tx_count[11]} {tx_count[12]} {tx_count[13]} {tx_count[14]} {tx_count[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe65]
set_property port_width 8 [get_debug_ports u_ila_0/probe65]
connect_debug_port u_ila_0/probe65 [get_nets [list {fifo_status[0]} {fifo_status[1]} {fifo_status[2]} {fifo_status[3]} {fifo_status[4]} {fifo_status[5]} {fifo_status[6]} {fifo_status[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe66]
set_property port_width 16 [get_debug_ports u_ila_0/probe66]
connect_debug_port u_ila_0/probe66 [get_nets [list {rx_count[0]} {rx_count[1]} {rx_count[2]} {rx_count[3]} {rx_count[4]} {rx_count[5]} {rx_count[6]} {rx_count[7]} {rx_count[8]} {rx_count[9]} {rx_count[10]} {rx_count[11]} {rx_count[12]} {rx_count[13]} {rx_count[14]} {rx_count[15]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe67]
set_property port_width 1 [get_debug_ports u_ila_0/probe67]
connect_debug_port u_ila_0/probe67 [get_nets [list uart_bridge_inst/axi_start_transaction]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe68]
set_property port_width 1 [get_debug_ports u_ila_0/probe68]
connect_debug_port u_ila_0/probe68 [get_nets [list uart_bridge_inst/axi_transaction_done]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe69]
set_property port_width 1 [get_debug_ports u_ila_0/probe69]
connect_debug_port u_ila_0/probe69 [get_nets [list uart_bridge_inst/uart_rx_inst/baud_tick]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe70]
set_property port_width 1 [get_debug_ports u_ila_0/probe70]
connect_debug_port u_ila_0/probe70 [get_nets [list bridge_busy]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe71]
set_property port_width 1 [get_debug_ports u_ila_0/probe71]
connect_debug_port u_ila_0/probe71 [get_nets [list bridge_enable]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe72]
set_property port_width 1 [get_debug_ports u_ila_0/probe72]
connect_debug_port u_ila_0/probe72 [get_nets [list uart_bridge_inst/builder_response_complete]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe73]
set_property port_width 1 [get_debug_ports u_ila_0/probe73]
connect_debug_port u_ila_0/probe73 [get_nets [list uart_bridge_inst/frame_builder/debug_cmd_state_active]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe74]
set_property port_width 1 [get_debug_ports u_ila_0/probe74]
connect_debug_port u_ila_0/probe74 [get_nets [list uart_bridge_inst/frame_parser/debug_crc_error]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe75]
set_property port_width 1 [get_debug_ports u_ila_0/probe75]
connect_debug_port u_ila_0/probe75 [get_nets [list uart_bridge_inst/frame_parser/debug_crc_match]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe76]
set_property port_width 1 [get_debug_ports u_ila_0/probe76]
connect_debug_port u_ila_0/probe76 [get_nets [list uart_bridge_inst/frame_builder/debug_response_type]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe77]
set_property port_width 1 [get_debug_ports u_ila_0/probe77]
connect_debug_port u_ila_0/probe77 [get_nets [list uart_bridge_inst/frame_parser/debug_rx_inc_bit]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe78]
set_property port_width 1 [get_debug_ports u_ila_0/probe78]
connect_debug_port u_ila_0/probe78 [get_nets [list uart_bridge_inst/frame_parser/debug_rx_rw_bit]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe79]
set_property port_width 1 [get_debug_ports u_ila_0/probe79]
connect_debug_port u_ila_0/probe79 [get_nets [list uart_bridge_inst/frame_builder/debug_sof_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe80]
set_property port_width 1 [get_debug_ports u_ila_0/probe80]
connect_debug_port u_ila_0/probe80 [get_nets [list uart_bridge_inst/frame_builder/debug_tx_fifo_wr_en_out]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe81]
set_property port_width 1 [get_debug_ports u_ila_0/probe81]
connect_debug_port u_ila_0/probe81 [get_nets [list uart_bridge_inst/debug_uart_rx_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe82]
set_property port_width 1 [get_debug_ports u_ila_0/probe82]
connect_debug_port u_ila_0/probe82 [get_nets [list uart_bridge_inst/uart_tx_inst/debug_uart_tx_bit]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe83]
set_property port_width 1 [get_debug_ports u_ila_0/probe83]
connect_debug_port u_ila_0/probe83 [get_nets [list uart_bridge_inst/debug_uart_tx_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe84]
set_property port_width 1 [get_debug_ports u_ila_0/probe84]
connect_debug_port u_ila_0/probe84 [get_nets [list internal_rst]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe85]
set_property port_width 1 [get_debug_ports u_ila_0/probe85]
connect_debug_port u_ila_0/probe85 [get_nets [list uart_bridge_inst/parser_frame_valid]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe86]
set_property port_width 1 [get_debug_ports u_ila_0/probe86]
connect_debug_port u_ila_0/probe86 [get_nets [list rx_fifo_full]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe87]
set_property port_width 1 [get_debug_ports u_ila_0/probe87]
connect_debug_port u_ila_0/probe87 [get_nets [list rx_fifo_high]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe88]
set_property port_width 1 [get_debug_ports u_ila_0/probe88]
connect_debug_port u_ila_0/probe88 [get_nets [list uart_bridge_inst/uart_rx_inst/rx_synced]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe89]
set_property port_width 1 [get_debug_ports u_ila_0/probe89]
connect_debug_port u_ila_0/probe89 [get_nets [list uart_bridge_inst/uart_rx_inst/sample_tick]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe90]
set_property port_width 1 [get_debug_ports u_ila_0/probe90]
connect_debug_port u_ila_0/probe90 [get_nets [list uart_bridge_inst/tx_fifo_rd_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe91]
set_property port_width 1 [get_debug_ports u_ila_0/probe91]
connect_debug_port u_ila_0/probe91 [get_nets [list uart_bridge_inst/tx_fifo_wr_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe92]
set_property port_width 1 [get_debug_ports u_ila_0/probe92]
connect_debug_port u_ila_0/probe92 [get_nets [list tx_ready]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe93]
set_property port_width 1 [get_debug_ports u_ila_0/probe93]
connect_debug_port u_ila_0/probe93 [get_nets [list uart_bridge_inst/tx_start_reg]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe94]
set_property port_width 1 [get_debug_ports u_ila_0/probe94]
connect_debug_port u_ila_0/probe94 [get_nets [list uart_bridge_inst/tx_start_req]]
set_property C_CLK_INPUT_FREQ_HZ 300000000 [get_debug_cores dbg_hub]
set_property C_ENABLE_CLK_DIVIDER false [get_debug_cores dbg_hub]
set_property C_USER_SCAN_CHAIN 1 [get_debug_cores dbg_hub]
connect_debug_port dbg_hub/clk [get_nets clk_IBUF_BUFG]
