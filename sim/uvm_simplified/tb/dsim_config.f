# DSIM Configuration File for Simplified AXIUART UVM Testbench
# UBUS-style simplified environment

# UVM Defines
+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
+define+DEFINE_SIM
+define+WAVES
+define+UVM_ENABLE_DEPRECATED_API
+define+UVM_REGEX_NO_DPI

# UVM Trace (critical for debug)
+UVM_OBJECTION_TRACE
+UVM_PHASE_TRACE
+UVM_SEQ_CHECKS

# Include paths
+incdir+../../../rtl/interfaces
+incdir+../../../rtl
+incdir+../sv
+incdir+.

# RTL Interface Definitions
../../../rtl/interfaces/uart_if.sv
../../../rtl/interfaces/axi4_lite_if.sv

# RTL Design Files
../../../rtl/fifo_sync.sv
../../../rtl/Uart_Rx.sv
../../../rtl/Uart_Tx.sv
../../../rtl/Crc8_Calculator.sv
../../../rtl/Frame_Parser.sv
../../../rtl/Frame_Builder.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Register_Block.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Uart_Axi4_Bridge.sv
../../../rtl/AXIUART_Top.sv

# Testbench Top Module (includes package and test_lib)
+incdir+.
./axiuart_tb_top.sv
