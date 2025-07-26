# MCP Setup for SqrtDirichlet

This project uses Model Context Protocol (MCP) tools for enhanced Lean 4 interactions.

## Components

### 1. MCP Tool Configuration (`.mcp/config.json`)
Defines available Lean-specific tools:
- `lean_goal`: Get proof goals at specific locations
- `lean_diagnostic_messages`: Get errors and warnings
- `lean_hover_info`: Get documentation at cursor
- `lean_leansearch`: Natural language theorem search
- `lean_loogle`: Type-based theorem search
- `lean_state_search`: Search based on proof state
- `lean_list_sorries`: Find all sorry placeholders

### 2. Claude Code Sub-agents (`.claude/agents/`)
Specialized AI assistants for different aspects of theorem proving:
- **lean-proof-repair**: Fix syntax errors and suggest tactics
- **cardinal-arithmetic**: Set theory and cardinality expert
- **topology-continuity**: Topological arguments and density
- **ultrafilter-model-theory**: Model theory and Dirichlet's theorem
- **proof-strategy**: Plan convoluted proof approaches

### 3. LeanTool Integration
LeanTool provides the backend for MCP tools with features:
- Interactive Lean checking via Pantograph
- Goal state extraction from `sorry` placeholders
- Property-based testing for Lean functions
- MCP server for tool execution

## Setup Instructions

### Prerequisites
1. Lean 4 (v4.22.0-rc4 for this project)
2. Poetry for Python dependency management
3. Python 3.11 or higher

### Installation
1. LeanTool is already included in this repository
2. Install dependencies:
   ```bash
   cd LeanTool
   poetry install
   lake exe cache get
   lake build
   ```

### Running the MCP Server
To start the LeanTool MCP server:
```bash
cd LeanTool
poetry run python leanmcp.py
```

For SSE mode (Server-Sent Events):
```bash
poetry run python leanmcp.py --sse --port 8080
```

## Usage

### With Claude Code
The sub-agents will automatically use MCP tools when needed. You can also explicitly request a sub-agent:
- "Use the cardinal-arithmetic sub agent to prove this cardinality inequality"
- "Ask the lean-proof-repair agent to fix these syntax errors"

### Direct Tool Usage
When the MCP server is running, tools can be invoked through the MCP protocol:
```python
# Example: Check Lean code
result = await check_lean(code="theorem foo : 2 + 2 = 4 := by sorry")
```

## Known Issues
- Lean version mismatch between LeanTool (4.20.1) and project (4.22.0-rc4) may cause compatibility issues
- Pantograph requires exact version alignment with the Lean toolchain

## Development Notes
- Test scripts are provided: `test_leantool.py` and `test_leantool_direct.py`
- The MCP configuration is project-local in `.mcp/`
- Sub-agents are defined in `.claude/agents/` with YAML frontmatter