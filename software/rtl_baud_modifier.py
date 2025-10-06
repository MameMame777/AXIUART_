#!/usr/bin/env python3
"""
RTL Parameter Modification Script for Low Baud Rate Testing
=========================================================
Temporarily modify UART RTL parameters for physical layer testing
"""

import os
import shutil
from datetime import datetime

class BaudRateModifier:
    """RTL parameter modification for baud rate testing"""
    
    def __init__(self):
        self.rtl_dir = "E:\\Nautilus\\workspace\\fpgawork\\AXIUART_\\rtl"
        self.backup_dir = "E:\\Nautilus\\workspace\\fpgawork\\AXIUART_\\rtl\\backup_original"
        self.files_to_modify = ["Uart_Tx.sv", "Uart_Rx.sv"]
        
    def create_backup(self):
        """Create backup of original RTL files"""
        if not os.path.exists(self.backup_dir):
            os.makedirs(self.backup_dir)
            
        print("🔄 Creating backup of original RTL files...")
        for filename in self.files_to_modify:
            src = os.path.join(self.rtl_dir, filename)
            dst = os.path.join(self.backup_dir, filename)
            shutil.copy2(src, dst)
            print(f"   ✅ Backed up {filename}")
    
    def modify_baud_rate(self, new_baud_rate=9600):
        """Modify RTL files for new baud rate"""
        print(f"\n🔧 Modifying RTL for {new_baud_rate} baud...")
        
        for filename in self.files_to_modify:
            filepath = os.path.join(self.rtl_dir, filename)
            
            # Read original file
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Replace BAUD_RATE parameter
            original_line = "    parameter int BAUD_RATE = 115200"
            new_line = f"    parameter int BAUD_RATE = {new_baud_rate}"
            
            if original_line in content:
                content = content.replace(original_line, new_line)
                print(f"   ✅ Modified {filename}: 115200 → {new_baud_rate}")
                
                # Write modified file
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(content)
            else:
                print(f"   ⚠️  Could not find baud rate parameter in {filename}")
    
    def restore_original(self):
        """Restore original RTL files from backup"""
        print("\n🔄 Restoring original RTL files...")
        
        if not os.path.exists(self.backup_dir):
            print("❌ No backup directory found!")
            return False
            
        for filename in self.files_to_modify:
            src = os.path.join(self.backup_dir, filename)
            dst = os.path.join(self.rtl_dir, filename)
            
            if os.path.exists(src):
                shutil.copy2(src, dst)
                print(f"   ✅ Restored {filename}")
            else:
                print(f"   ❌ Backup not found for {filename}")
        
        return True
    
    def generate_build_script(self, baud_rate):
        """Generate build script for modified RTL"""
        script_content = f"""#!/bin/bash
# Automated build script for {baud_rate} baud UART testing
# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

echo "🏗️  Building FPGA bitstream with {baud_rate} baud UART..."

# Navigate to Vivado project directory
cd "E:/Nautilus/workspace/fpgawork/AXIUART_/PandR/vivado"

# Run Vivado synthesis and implementation
vivado -mode batch -source build_project.tcl

echo "✅ Build completed for {baud_rate} baud configuration"
echo "📋 Next steps:"
echo "   1. Program FPGA with new bitstream"
echo "   2. Run Python test at {baud_rate} baud"
echo "   3. Compare results with 115200 baud"
"""
        
        script_path = os.path.join(self.rtl_dir, f"build_{baud_rate}_baud.sh")
        with open(script_path, 'w', encoding='utf-8') as f:
            f.write(script_content)
        print(f"   📝 Generated build script: {script_path}")

def main():
    print("🎯 RTL Baud Rate Modification Tool")
    print("=" * 50)
    print("For physical layer investigation and protocol testing")
    
    modifier = BaudRateModifier()
    
    print("\n📋 Available Options:")
    print("1. Create backup and modify for 9600 baud")
    print("2. Create backup and modify for 19200 baud") 
    print("3. Create backup and modify for 38400 baud")
    print("4. Restore original 115200 baud")
    print("5. View current configuration")
    
    choice = input("\nSelect option (1-5): ")
    
    if choice == "1":
        modifier.create_backup()
        modifier.modify_baud_rate(9600)
        modifier.generate_build_script(9600)
        print("\n🎯 Next Steps:")
        print("   1. Run Vivado synthesis with modified RTL")
        print("   2. Program FPGA with new bitstream")
        print("   3. Test Python communication at 9600 baud")
        
    elif choice == "2":
        modifier.create_backup()
        modifier.modify_baud_rate(19200)
        modifier.generate_build_script(19200)
        print("\n🎯 Next Steps: Build and test at 19200 baud")
        
    elif choice == "3":
        modifier.create_backup()
        modifier.modify_baud_rate(38400)
        modifier.generate_build_script(38400)
        print("\n🎯 Next Steps: Build and test at 38400 baud")
        
    elif choice == "4":
        if modifier.restore_original():
            print("✅ Original 115200 baud configuration restored")
        
    elif choice == "5":
        print("\n📋 Current Configuration:")
        for filename in modifier.files_to_modify:
            filepath = os.path.join(modifier.rtl_dir, filename)
            if os.path.exists(filepath):
                with open(filepath, 'r') as f:
                    for i, line in enumerate(f, 1):
                        if "BAUD_RATE =" in line:
                            print(f"   {filename} line {i}: {line.strip()}")
    
    print(f"\n🎉 RTL modification completed")

if __name__ == "__main__":
    main()