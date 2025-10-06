#!/usr/bin/env python3
"""
Remove mark_debug attributes from RTL files
"""

import os
import re
import glob

def remove_mark_debug_from_file(file_path):
    """Remove (* mark_debug = "true" *) from a single file"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Pattern to match (* mark_debug = "true" *)
        # Handle various spacing patterns
        pattern = r'\(\*\s*mark_debug\s*=\s*"true"\s*\*\)\s*'
        
        # Count matches before removal
        matches = re.findall(pattern, content)
        count = len(matches)
        
        if count > 0:
            # Remove the pattern
            new_content = re.sub(pattern, '', content)
            
            # Write back to file
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            
            print(f"✅ {file_path}: Removed {count} mark_debug attributes")
            return count
        else:
            print(f"⚪ {file_path}: No mark_debug attributes found")
            return 0
            
    except Exception as e:
        print(f"❌ {file_path}: Error - {e}")
        return 0

def main():
    print("🔧 Removing mark_debug attributes from RTL files")
    print("=" * 60)
    
    # Get all .sv files in rtl directory
    rtl_dir = r"E:\Nautilus\workspace\fpgawork\AXIUART_\rtl"
    sv_files = glob.glob(os.path.join(rtl_dir, "*.sv"))
    
    total_removed = 0
    files_modified = 0
    
    for file_path in sv_files:
        count = remove_mark_debug_from_file(file_path)
        total_removed += count
        if count > 0:
            files_modified += 1
    
    print(f"\n📊 Summary:")
    print(f"   Files processed: {len(sv_files)}")
    print(f"   Files modified: {files_modified}")
    print(f"   Total mark_debug removed: {total_removed}")
    print(f"\n🎉 mark_debug cleanup completed!")

if __name__ == "__main__":
    main()