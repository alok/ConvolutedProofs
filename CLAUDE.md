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