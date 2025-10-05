#!/bin/bash
# Automated build script for 9600 baud UART testing
# Generated: 2025-10-06 06:40:40

echo "🏗️  Building FPGA bitstream with 9600 baud UART..."

# Navigate to Vivado project directory
cd "E:/Nautilus/workspace/fpgawork/AXIUART_/PandR/vivado"

# Run Vivado synthesis and implementation
vivado -mode batch -source build_project.tcl

echo "✅ Build completed for 9600 baud configuration"
echo "📋 Next steps:"
echo "   1. Program FPGA with new bitstream"
echo "   2. Run Python test at 9600 baud"
echo "   3. Compare results with 115200 baud"
