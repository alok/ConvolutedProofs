#!/usr/bin/env python3
"""Test script to verify LeanTool functionality."""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), 'LeanTool'))

import asyncio
from leantool import run_lean, extract_sorry_data_from_lean, get_lean_path

async def test_leantool():
    """Test basic LeanTool functionality."""
    
    # Test 1: Check if Lean is accessible
    print("Test 1: Checking Lean path...")
    lean_path = await get_lean_path()
    print(f"Lean found at: {lean_path}")
    
    # Test 2: Run Lean on a simple file
    print("\nTest 2: Running Lean on SqrtDirichlet.lean...")
    with open("SqrtDirichlet.lean", "r") as f:
        lean_code = f.read()
    
    result = await run_lean(lean_code)
    print(f"Exit code: {result['returncode']}")
    
    if result['returncode'] != 0:
        print("Errors found:")
        print(result['stderr'][:500] + "..." if len(result['stderr']) > 500 else result['stderr'])
    else:
        print("No errors found!")
    
    # Test 3: Extract sorry data
    print("\nTest 3: Extracting sorry data...")
    sorry_data = await extract_sorry_data_from_lean(lean_code)
    
    if sorry_data:
        print(f"Found {len(sorry_data)} sorry placeholders:")
        for i, sorry in enumerate(sorry_data):
            print(f"\nSorry {i+1}:")
            print(f"  Position: {sorry.get('pos', 'Unknown')}")
            print(f"  Goal: {sorry.get('goal', 'Unknown')[:100]}...")
    else:
        print("No sorry placeholders found or extraction failed.")
    
    return result['returncode'] == 0

if __name__ == "__main__":
    success = asyncio.run(test_leantool())
    sys.exit(0 if success else 1)