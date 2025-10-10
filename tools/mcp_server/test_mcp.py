#!/usr/bin/env python3
"""
Test script for AXIUART Verification MCP Server
Validates MCP protocol functionality and tool responses
"""

import json
import subprocess
import sys
from pathlib import Path

def test_mcp_server():
    """Test MCP server functionality"""
    print("🧪 Testing AXIUART Verification MCP Server")
    print("=" * 50)
    
    server_path = Path(__file__).parent / "src" / "standalone_server.py"
    
    # Test requests
    test_cases = [
        {
            "name": "Initialize",
            "request": {
                "jsonrpc": "2.0",
                "method": "initialize",
                "params": {},
                "id": 1
            }
        },
        {
            "name": "List Tools",
            "request": {
                "jsonrpc": "2.0",
                "method": "tools/list",
                "params": {},
                "id": 2
            }
        },
        {
            "name": "Check Environment",
            "request": {
                "jsonrpc": "2.0",
                "method": "tools/call",
                "params": {
                    "name": "check_environment",
                    "arguments": {"verbose": False}
                },
                "id": 3
            }
        },
        {
            "name": "Get Phase Guidance",
            "request": {
                "jsonrpc": "2.0",
                "method": "tools/call",
                "params": {
                    "name": "get_phase_guidance",
                    "arguments": {}
                },
                "id": 4
            }
        },
        {
            "name": "List Resources",
            "request": {
                "jsonrpc": "2.0",
                "method": "resources/list",
                "params": {},
                "id": 5
            }
        }
    ]
    
    for test_case in test_cases:
        print(f"\n🔍 Testing: {test_case['name']}")
        print("-" * 30)
        
        try:
            # Convert request to JSON
            request_json = json.dumps(test_case['request']) + "\n"
            
            # Execute server with request
            process = subprocess.run(
                [sys.executable, str(server_path)],
                input=request_json,
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if process.returncode == 0:
                try:
                    response = json.loads(process.stdout.strip())
                    print(f"✅ Success: {test_case['name']}")
                    
                    # Print relevant parts of response
                    if "result" in response:
                        if test_case['name'] == "List Tools" and "tools" in response["result"]:
                            tools = response["result"]["tools"]
                            print(f"   Found {len(tools)} tools:")
                            for tool in tools:
                                print(f"   - {tool.get('name', 'unnamed')}")
                        elif test_case['name'] == "Check Environment" and "content" in response["result"]:
                            content = response["result"]["content"]
                            if content and len(content) > 0:
                                text = content[0].get("text", "")
                                lines = text.split('\n')[:5]  # First 5 lines
                                print(f"   Response preview:")
                                for line in lines:
                                    if line.strip():
                                        print(f"   {line}")
                        elif test_case['name'] == "List Resources" and "resources" in response["result"]:
                            resources = response["result"]["resources"]
                            print(f"   Found {len(resources)} resources:")
                            for resource in resources:
                                print(f"   - {resource.get('uri', 'no-uri')}")
                    
                except json.JSONDecodeError as e:
                    print(f"⚠️  JSON decode error: {e}")
                    print(f"   Raw output: {process.stdout[:200]}")
            else:
                print(f"❌ Failed: {test_case['name']}")
                print(f"   Return code: {process.returncode}")
                if process.stderr:
                    print(f"   Error: {process.stderr[:200]}")
                
        except subprocess.TimeoutExpired:
            print(f"⏰ Timeout: {test_case['name']}")
        except Exception as e:
            print(f"❌ Exception: {test_case['name']} - {e}")
    
    print("\n" + "=" * 50)
    print("🏁 MCP Server Test Complete")

if __name__ == "__main__":
    test_mcp_server()