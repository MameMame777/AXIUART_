# UVM Configuration File for UART-AXI Bridge Verification
# Purpose: Working UVM testbench with simplified agent structure
# Date: August 12, 2025

# Timescale
+timescale+1ns/1ps

# UVM Library
-uvm 1.2

# UVM include path
+incdir+C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0\uvm\1.2\src

# Include directories
+incdir+../../rtl/interfaces
+incdir+../../rtl/hdl  
+incdir+../../sim/uvm
+incdir+../../sim/uvm/tests

# RTL Interface packages and files
../../rtl/interfaces/axi4_lite_pkg.sv
../../rtl/interfaces/axi4_lite_if.sv
../../rtl/interfaces/uart_if.sv

# RTL Design files (DUT)
../../rtl/hdl/Baud_Generator.sv
../../rtl/hdl/Uart_Tx.sv
../../rtl/hdl/Uart_Rx.sv
../../rtl/hdl/Dual_Port_Fifo.sv
../../rtl/hdl/Uart_Controller.sv
../../rtl/hdl/Register_Bank.sv
../../rtl/hdl/Interrupt_Controller.sv
../../rtl/hdl/Protocol_Handler.sv
../../rtl/hdl/Axi4_Lite_Slave.sv
../../rtl/hdl/Led_pwm.sv
../../rtl/hdl/Uart_Axi4_Bridge.sv

# Simple UVM Test Package (working package)
../../sim/uvm/packages/uart_axi_test_pkg.sv

# UVM Testbench Top
../../sim/tb/uart_axi_tb_clean.sv
