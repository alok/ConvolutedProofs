#!/usr/bin/env python3
"""Direct test of LeanTool check_lean_code function."""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), 'LeanTool'))

import asyncio
from leantool import check_lean_code

async def test_check_lean():
    """Test check_lean_code function."""
    
    # Simple test code with a sorry
    test_code = """
import Mathlib

theorem test_theorem : 2 + 2 = 4 := by
  sorry
"""
    
    print("Testing LeanTool with simple theorem...")
    result = await check_lean_code(test_code, json_output=True)
    
    print(f"\nResult: {result}")
    
    if result.get('success'):
        print("\nLean check succeeded!")
        output = result.get('output', {})
        if isinstance(output, dict) and 'sorries' in output:
            print(f"Found {len(output['sorries'])} sorry placeholders")
            for i, sorry in enumerate(output['sorries']):
                print(f"\nSorry {i+1}:")
                print(f"  Goal: {sorry.get('goal', 'Unknown')}")
    else:
        print(f"\nError: {result.get('error', 'Unknown error')}")
    
    return result.get('success', False)

if __name__ == "__main__":
    success = asyncio.run(test_check_lean())
    sys.exit(0 if success else 1)