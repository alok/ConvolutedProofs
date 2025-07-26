# MCP Setup for SqrtDirichlet

This project uses Model Context Protocol (MCP) tools for enhanced Lean 4 interactions.

## Components

### 1. MCP Server Configuration (`.mcp.json`)
Defines the local MCP server for Lean tools:
```json
{
  "mcpServers": {
    "lean-tools": {
      "command": "node",
      "args": ["/Users/alokbeniwal/SqrtDirichlet/.mcp/server.js"],
      "env": {}
    }
  }
}
```

### 2. Available MCP Tools
The server provides these Lean-specific tools:
- `lean_goal`: Get proof goals at specific locations (placeholder)
- `lean_diagnostic_messages`: Get errors and warnings from lake build
- `lean_build`: Build a Lean file or project with lake

### 3. Claude Code Sub-agents (`.claude/agents/`)
Specialized AI assistants for different aspects of theorem proving:
- **lean-proof-repair**: Fix syntax errors and suggest tactics
- **cardinal-arithmetic**: Set theory and cardinality expert
- **topology-continuity**: Topological arguments and density
- **ultrafilter-model-theory**: Model theory and Dirichlet's theorem
- **proof-strategy**: Plan convoluted proof approaches

## Setup Instructions

### Prerequisites
1. Lean 4 (v4.22.0-rc4 for this project)
2. Node.js 16 or higher
3. npm for package management

### Installation
The MCP server is already configured. To install dependencies:
```bash
cd .mcp
npm install
```

### Using with Claude Code
The MCP server will be automatically started by Claude Code when you open the project.
The configuration in `.mcp.json` tells Claude Code how to run the server.

## Usage

### With Claude Code
The sub-agents will automatically use MCP tools when needed. You can also explicitly request a sub-agent:
- "Use the cardinal-arithmetic sub agent to prove this cardinality inequality"
- "Ask the lean-proof-repair agent to fix these syntax errors"

### Available Commands
- Build the project: The MCP tools can run `lake build` 
- Get diagnostics: Retrieve error messages from Lean files
- Future: Goal state inspection (requires Lean LSP integration)

## Development Notes
- The MCP server is implemented in `.mcp/server.js`
- Configuration is in `.mcp.json` (project scope)
- Sub-agents are defined in `.claude/agents/` with YAML frontmatter