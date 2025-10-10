# DSIM Configuration for Register Block Minimal Test
# Purpose: Minimal file list for focused debugging

# Timescale
+timescale+1ns/1ps

# UVM defines
+define+UVM_NO_DEPRECATED
+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
+define+ENABLE_DEBUG

# Include directories
+incdir+.
+incdir+tests
+incdir+tb
+incdir+../../rtl/interfaces

# Interface files
../../rtl/interfaces/axi4_lite_if.sv

# RTL files - only what we need
../../rtl/Register_Block.sv

# UVM library
-uvm 1.2

# Test files
tests/register_block_minimal_test.sv
tb/register_block_minimal_tb.sv

# Compilation options
-sv
-work dsim_work

# Wave dumping with proper access
+acc+rwb
-waves register_block_minimal.mxd