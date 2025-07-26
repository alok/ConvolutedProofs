# Convoluted Proofs

A collection of absurdly sophisticated proofs of simple mathematical facts in Lean 4.

## Overview

This project demonstrates how simple mathematical facts can be proven using unnecessarily complex mathematical machinery. It's inspired by the MathOverflow question ["Awfully sophisticated proof for simple facts"](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts) and Asaf Karagila's proof of the irrationality of √2 using ultrafilters.

## Theorems Proved

### 1. Irrationality of √2 (`irrational_sqrt_2`)
**Statement**: √2 is irrational.

**Convoluted approach**: 
- Uses Dirichlet's theorem on primes in arithmetic progressions
- Constructs a non-principal ultrafilter on an infinite set of primes
- Applies quadratic reciprocity and properties of finite fields
- Originally intended to use model theory and ultraproducts (simplified in implementation)

**Reference**: Based on [Asaf Karagila's proof](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational)

### 2. Existence of Discontinuous Functions (`discontinuous_function_exists`)
**Statement**: There exists a function from ℝ to ℝ that is not continuous.

**Convoluted approach**:
- Uses cardinal arithmetic and cardinality arguments
- Shows that if all functions were continuous, we'd have #(ℝ → ℝ) ≤ #(ℚ → ℝ)
- Applies the fact that continuous functions are determined by their values on dense subsets
- Derives a contradiction using Cantor's theorem

**Reference**: [MathOverflow discussion](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts)

### 3. Continuity of Constant Functions (`constant_one_continuous`)
**Statement**: The constant function f(x) = 1 is continuous.

**Convoluted approach**:
- References the Weierstrass approximation theorem
- Mentions the Arzelà-Ascoli theorem
- Invokes Stone-Weierstrass theorem
- Discusses measure theory and functional analysis concepts
- Finally uses the trivial fact that constant functions are continuous

**Inspiration**: Carleson's theorem machinery

## Building the Project

1. Install Lean 4 following the [official instructions](https://leanprover.github.io/lean4/doc/setup.html)
2. Clone this repository
3. Run `lake build` in the project directory

## Mathematical Background

The project showcases how advanced mathematical concepts can be (mis)used to prove elementary results:

- **Model Theory**: Ultraproducts, Łoś's theorem, first-order structures
- **Number Theory**: Dirichlet's theorem, quadratic reciprocity
- **Set Theory**: Cardinal arithmetic, Cantor's theorem
- **Topology**: Density arguments, Baire category theorem
- **Functional Analysis**: Approximation theorems, measure theory

## Contributing

Feel free to add your own convoluted proofs! The more sophisticated the machinery for proving simple facts, the better.

## License

Apache 2.0