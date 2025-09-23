# USB-UART-AXI4 Bridge Constraint File for Vivado
# Target Board: Zybo Z7-20
# Date: September 23, 2025
# Description: Production constraint file aligned with AXIUART_Top.sv RTL implementation
# Reference: RTL signals in AXIUART_Top.sv

###################################################################################
# Clock Constraints
###################################################################################

# System Clock - 50MHz input (matching RTL CLK_FREQ_HZ default)
# Note: RTL default is 50MHz, but Zybo Z7-20 provides 125MHz - adjust parameter accordingly
set_property -dict { PACKAGE_PIN K17   IOSTANDARD LVCMOS33 } [get_ports { clk }]
create_clock -add -name sys_clk_pin -period 8.00 -waveform {0 4} [get_ports { clk }]

###################################################################################
# Reset Constraints  
###################################################################################

# External reset input (active high, synchronous)
set_property -dict { PACKAGE_PIN K18   IOSTANDARD LVCMOS33 } [get_ports { rst }]

###################################################################################
# UART Interface - JB Connector (Pmod USBUART)
###################################################################################

# UART Transmit Data (FPGA TX → Pmod RX) - matches RTL signal uart_tx
set_property -dict { PACKAGE_PIN W8    IOSTANDARD LVCMOS33 } [get_ports { uart_tx }]

# UART Receive Data (Pmod TX → FPGA RX) - matches RTL signal uart_rx
set_property -dict { PACKAGE_PIN U7    IOSTANDARD LVCMOS33 } [get_ports { uart_rx }]

###################################################################################
# System Status Outputs (Optional - for debugging/monitoring)
###################################################################################

# System Ready Indicator (LED0)
# set_property -dict { PACKAGE_PIN M14   IOSTANDARD LVCMOS33 } [get_ports { system_ready }]

# System Busy Indicator (LED1) 
# set_property -dict { PACKAGE_PIN M15   IOSTANDARD LVCMOS33 } [get_ports { system_busy }]

# System Error Indicator (LED2)
# set_property -dict { PACKAGE_PIN G14   IOSTANDARD LVCMOS33 } [get_ports { system_error }]

###################################################################################
# Timing Constraints
###################################################################################

# UART Interface Timing Constraints
# UART signals are asynchronous but need proper timing relationship with system clock
set_input_delay -clock [get_clocks sys_clk_pin] -min 1.0 [get_ports {uart_rx}]
set_input_delay -clock [get_clocks sys_clk_pin] -max 3.0 [get_ports {uart_rx}]

set_output_delay -clock [get_clocks sys_clk_pin] -min 1.0 [get_ports {uart_tx}]
set_output_delay -clock [get_clocks sys_clk_pin] -max 3.0 [get_ports {uart_tx}]

# False path constraints for asynchronous UART receive signal
# UART RX is asynchronous and handled by oversampling in RTL
set_false_path -from [get_ports uart_rx] -to [get_clocks sys_clk_pin]

# Reset signal is external and asynchronous
set_false_path -from [get_ports rst] -to [all_clocks]

# Optional: False paths for status output LEDs if implemented
# set_false_path -to [get_ports {system_ready system_busy system_error}]

###################################################################################
# Physical Constraints
###################################################################################

# Set slew rate and drive strength for UART output signals
# Slower slew rate reduces EMI for UART communication
set_property SLEW SLOW [get_ports {uart_tx}]
set_property DRIVE 8 [get_ports {uart_tx}]

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
