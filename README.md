# Convoluted Proofs

A collection of absurdly sophisticated proofs of simple mathematical facts in Lean 4.

## Overview

This project demonstrates how simple mathematical facts can be proven using unnecessarily complex mathematical machinery. It's inspired by the MathOverflow question ["Awfully sophisticated proof for simple facts"](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts) and Asaf Karagila's proof of the irrationality of √2 using ultrafilters.

## Theorems Proved

### 1. Irrationality of √2 (`irrational_sqrt_2`)
**Statement**: √2 is irrational.

**Convoluted approach**: 
- Uses Dirichlet's theorem on primes in arithmetic progressions to get infinitely many primes ≡ 3 (mod 8)
- Constructs a non-principal ultrafilter on this infinite set using the hyperfilter
- Applies quadratic reciprocity to show 2 is not a square mod p for these primes
- Derives a contradiction by showing if √2 = a/b, then 2 would be a square mod p

**Reference**: Based on [Asaf Karagila's proof](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational) (see comments)

### 2. Bounded Periodic Functions are A.E. Continuous (`bounded_periodic_ae_eq_continuous`)
**Statement**: Every bounded 2π-periodic function ℝ → ℂ equals a continuous function almost everywhere.

**Convoluted approach**:
- Works on the circle T = ℝ/(2πℤ) with Haar measure
- Invokes Carleson's theorem (1966) on pointwise convergence of Fourier series
- Uses Fejér sums (Cesàro means) and their uniform convergence
- References Calderón-Zygmund theory, singular integrals, and the Hilbert transform
- Mentions Hardy-Littlewood maximal theorem

**Note**: Proof left incomplete with `sorry`

### 3. Indicator Function is A.E. Continuous (`indicator_ae_continuous`)
**Statement**: The indicator function of [0,1] equals a continuous function almost everywhere.

**Convoluted approach**:
- Extends indicator to a 2-periodic function and computes Fourier coefficients
- Applies Carleson's theorem for pointwise convergence
- Uses Fejér sums (continuous trigonometric polynomials)
- Invokes Egorov's theorem to upgrade a.e. convergence
- References distribution theory, Sobolev embeddings, and BV functions

**Note**: This is a false statement - the "proof" is intentionally flawed! Indicator functions are not a.e. equal to continuous functions.

### 4. Bounded Functions Have Antiderivatives (`bounded_has_antiderivative`)
**Statement**: Every bounded function on [0,1] has an antiderivative.

**Convoluted approach**:
- Extends function periodically and considers its Fourier series
- Uses Carleson's theorem for pointwise convergence a.e.
- Constructs antiderivative by formally integrating Fourier series term by term
- Applies uniform convergence to show differentiability
- References Paley-Wiener theorems, Littlewood-Paley theory, and Calderón-Zygmund decomposition

**Reference**: Direct example from the MathOverflow thread - using Carleson's theorem to prove Riemann integrability

**Note**: Proof incomplete with `sorry`

### 5. Existence of Discontinuous Functions (`discontinuous_function_exists`)
**Statement**: There exists a function from ℝ to ℝ that is not continuous.

**Convoluted approach**:
- Proof by contradiction assuming all functions are continuous
- Uses cardinal arithmetic: if all functions were continuous, then #(ℝ → ℝ) ≤ #(ℚ → ℝ)
- Applies density of ℚ in ℝ and that continuous functions are determined by values on dense subsets
- Shows this implies 𝔠^𝔠 ≤ 𝔠^ℵ₀ = 𝔠
- Derives contradiction using Cantor's theorem: 𝔠 < 𝔠^𝔠

**Reference**: [MathOverflow discussion](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts)

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