See @SqrtDirichlet.lean and its comment.

The GOAL is to use convoluted proofs, so more direct ones are not the goal.

## Specialized Sub-agents

The following sub-agents are available in `.claude/agents/` to help with specific aspects of the proofs:

### lean-proof-repair
Expert in fixing Lean syntax errors and suggesting appropriate tactics based on goal states. Invoke when you encounter:
- Syntax errors in Lean files
- Failed tactic applications
- Need for tactic suggestions for `sorry` placeholders

### cardinal-arithmetic  
Specialist in set theory, cardinal arithmetic, and cardinality proofs including Cantor's theorem. Essential for:
- The discontinuous function proof's cardinality argument
- Cardinal inequalities like #(ℝ → ℝ) > #ℝ
- Applications of Schröder-Bernstein theorem

### topology-continuity
Expert in topological arguments, density, and continuity. Crucial for:
- Density arguments (ℚ dense in ℝ)
- Proving continuous functions equal via agreement on dense subset
- IsClosed and IsOpen properties

### ultrafilter-model-theory
Specialist in ultrafilters, Łoś's theorem, and model-theoretic constructions. Key for:
- The √2 irrationality proof via Dirichlet's theorem
- Ultraproduct constructions
- Transfer principles and non-standard models

### proof-strategy
High-level proof planning focused on finding convoluted but correct approaches. Consult for:
- Alternative proof strategies
- Connecting disparate mathematical areas
- Finding sophisticated machinery for simple results

These sub-agents can be invoked automatically by Claude Code or explicitly requested.

## MCP Tools for Lean Development

The project uses two MCP servers configured in `.mcp.json`:

### 1. lean-lsp-mcp
Provides Lean language server protocol integration with these tools:

- **`lean_diagnostic_messages`**: Get all diagnostic messages (errors, warnings, infos) for a Lean file
- **`lean_goal`**: Get the proof goals (proof state) at a specific location - main tool for understanding proof state evolution!
- **`lean_term_goal`**: Get the expected type (term goal) at a specific location
- **`lean_hover_info`**: Get hover information (documentation) for symbols
- **`lean_completions`**: Code auto-completion for available identifiers or imports
- **`lean_multi_attempt`**: Try multiple Lean code snippets at a line and return goal state and diagnostics
- **`lean_declaration_file`**: Get file contents where a symbol is declared

Search tools (rate limited to 3 requests/30s):
- **`lean_leansearch`**: Natural language and Lean term search
- **`lean_loogle`**: Search by constant, lemma name, type shape, or conclusion
- **`lean_state_search`**: Search theorems based on proof state
- **`lean_hammer_premise`**: Search premises using Lean Hammer

### 2. leanexplore
Search and exploration tool for Lean mathematics:
- **`search`**: Search Lean statement groups by query
- **`get_by_id`**: Retrieve statement groups by ID
- **`get_dependencies`**: Get direct dependencies for statement groups

## Lean 4 Development Guidelines

### Best Practices
- Use named holes (`?foo`) for incremental development and well-typed fragments
- Wrap reserved names in «guillemets» when needed
- Implement notation typeclasses like `GetElem`, `Add`, etc where appropriate
- Practice "sorry-friendly programming": Use specs with `sorry` instead of comments
- Decompose proofs until tools like `canonical`, `grind`, and `simp` dissolve the pieces
- Run `lake build` frequently for constant feedback

### Common Errors and Solutions
- **"unexpected token 'namespace'"**: Module/doc comment placed incorrectly (should be after imports)
- **"unexpected token"**: Often caused by misplaced docstrings - use multiline comments instead
- **Natural number subtraction**: Be careful with `Nat` subtraction - it truncates at 0
- **Division by 0**: Lean defines division by 0, but results may be unexpected

### Import and Module Structure
- Imports MUST come before any syntax elements, including module and doc comments
- Set `linter.missingDocs = true` and `relaxedAutoImplicit = false` in `lakefile.lean`

### Building and Testing
```bash
# Build Lean project
lake build

# Build with verbose output for debugging
lake build --verbose

# Clean build artifacts if needed
lake clean
```