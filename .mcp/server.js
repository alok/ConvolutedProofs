#!/usr/bin/env node

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ListToolsRequestSchema } from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';
import { exec } from 'child_process';
import { promisify } from 'util';
import { readFile } from 'fs/promises';
import path from 'path';

const execAsync = promisify(exec);

// Tool schemas
const tools = [
  {
    name: 'lean_goal',
    description: 'Get the proof goals (proof state) at a specific location in a Lean file',
    inputSchema: {
      type: 'object',
      properties: {
        file_path: { type: 'string', description: 'Absolute path to Lean file' },
        line: { type: 'integer', description: 'Line number (1-indexed)' },
        column: { type: 'integer', description: 'Column number (1-indexed, optional)' }
      },
      required: ['file_path', 'line']
    }
  },
  {
    name: 'lean_diagnostic_messages',
    description: 'Get all diagnostic messages (errors, warnings, infos) for a Lean file',
    inputSchema: {
      type: 'object',
      properties: {
        file_path: { type: 'string', description: 'Absolute path to Lean file' }
      },
      required: ['file_path']
    }
  },
  {
    name: 'lean_build',
    description: 'Build a Lean file or project with lake',
    inputSchema: {
      type: 'object',
      properties: {
        file_path: { type: 'string', description: 'Path to Lean file or project directory' }
      },
      required: ['file_path']
    }
  }
];

// Create server
const server = new Server(
  {
    name: 'lean-tools',
    version: '1.0.0',
  },
  {
    capabilities: {
      tools: {},
    },
  }
);

// Handle list tools request
server.setRequestHandler(ListToolsRequestSchema, async () => {
  return {
    tools,
  };
});

// Handle tool calls
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  try {
    switch (name) {
      case 'lean_goal': {
        // For now, return a placeholder - would need Lean LSP integration
        return {
          content: [
            {
              type: 'text',
              text: `Goal state at ${args.file_path}:${args.line}:${args.column || 0} would require Lean LSP integration`
            }
          ]
        };
      }

      case 'lean_diagnostic_messages': {
        // Run lake build and capture output
        const dir = path.dirname(args.file_path);
        try {
          const { stdout, stderr } = await execAsync('lake build', { cwd: dir });
          return {
            content: [
              {
                type: 'text',
                text: stderr || 'No diagnostic messages found'
              }
            ]
          };
        } catch (error) {
          return {
            content: [
              {
                type: 'text',
                text: `Error: ${error.message}\n${error.stderr || ''}`
              }
            ]
          };
        }
      }

      case 'lean_build': {
        const dir = args.file_path.endsWith('.lean') 
          ? path.dirname(args.file_path)
          : args.file_path;
        
        try {
          const { stdout, stderr } = await execAsync('lake build', { cwd: dir });
          return {
            content: [
              {
                type: 'text',
                text: `Build successful\n${stdout}`
              }
            ]
          };
        } catch (error) {
          return {
            content: [
              {
                type: 'text',
                text: `Build failed:\n${error.stderr || error.message}`
              }
            ]
          };
        }
      }

      default:
        throw new Error(`Unknown tool: ${name}`);
    }
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: `Error: ${error.message}`
        }
      ],
      isError: true,
    };
  }
});

// Start server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Lean MCP server running...');
}

main().catch(console.error);