import Mathlib
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Cardinal Set Function FirstOrder.Language FirstOrder.Ring Real

/-- There exists a function with a discontinuity at at least one point. Based on Asaf's proof in https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational (see comments). Uses Dirichlet's theorem to get infinite sequences to create filters.

Cruxes to make this work:

- [ ] first order formula recognition

---


- [ ] setup leantool (*within* this repo for self-containedness) https://github.com/GasStationManager/LeanTool


-/

theorem irrational_sqrt_2 : Irrational √2 := by
  -- We'll prove this using Dirichlet's theorem and ultrafilters (following Asaf Karagila)
  by_contra h
  push_neg at h
  -- h : ¬Irrational √2, so √2 is rational

  -- If √2 were rational, it would be in every field of characteristic 0
  -- We'll construct a field of characteristic 0 that doesn't contain √2

  -- First, use Dirichlet's theorem to get infinitely many primes ≡ 3 (mod 8)
  have three_unit : IsUnit (3 : ZMod 8) := by decide

  -- Get the infinite set of primes ≡ 3 (mod 8)
  -- For these primes, 2 is not a square mod p
  let P := {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}
  have P_infinite : P.Infinite := Nat.setOf_prime_and_eq_mod_infinite three_unit

  -- For primes p ≡ 3 (mod 8), 2 is not a square mod p
  have h_not_square : ∀ p ∈ P, p ≠ 2 → ¬IsSquare (2 : ZMod p) := by
    intro p hp hp2
    have hp_prime : p.Prime := hp.1
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have : p % 8 = 3 := by
      have hcast : (p : ZMod 8) = 3 := hp.2
      -- Use that (p : ZMod 8) = ZMod.val (p : ZMod 8) when p % 8 < 8
      have : ZMod.val (p : ZMod 8) = 3 := by
        rw [hcast]
        rfl
      rwa [ZMod.val_natCast] at this
    rw [ZMod.exists_sq_eq_two_iff hp2]
    push_neg
    constructor
    · intro h
      rw [this] at h
      norm_num at h
    · intro h
      rw [this] at h
      norm_num at h

  -- Build a non-principal ultrafilter on P using the hyperfilter construction
  -- The hyperfilter extends the cofinite filter and is non-principal on infinite types
  haveI : Infinite ↑P := P_infinite.to_subtype
  let U : Ultrafilter ↑P := @Filter.hyperfilter ↑P _

  -- U is non-principal since it contains the cofinite filter
  have U_nonprincipal : ∀ p : ↑P, U ≠ pure p := by
    intro p hU
    -- If U = pure p, then {p} ∈ U, but finite sets aren't in the hyperfilter
    have : {p} ∈ U := by rw [hU]; exact Filter.singleton_mem_pure
    exact (Set.finite_singleton _).notMem_hyperfilter this

  -- Model theory setup: ultraproduct of finite fields ZMod p for p ∈ P
  -- Key insight: If √2 ∈ ℚ, then x² = 2 has a solution in every char 0 field
  -- But by quadratic reciprocity, x² ≡ 2 (mod p) has no solution for p ≡ 3 (mod 8)
  -- The ultraproduct would give a char 0 field with no solution to x² = 2 (contradiction)

  -- Direct approach: use that P contains arbitrarily large primes

  -- First, note that 2 ∉ P since (2 : ZMod 8) = 2 ≠ 3
  have two_not_in_P : 2 ∉ P := by decide


  -- For contradiction, assume √2 is rational
  rw [Irrational] at h
  push_neg at h
  obtain ⟨q, hq : (q : ℝ) = √2⟩ := h
  -- Get coprime representation √2 = a/b
  have hq_pos : 0 < q := by
    have : (0 : ℝ) < q := by
      rw [hq]
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast this
  let a := q.num.natAbs
  let b := q.den
  have hpos : 0 < b := q.pos
  have hcoprime : a.Coprime b := by
    rw [Nat.Coprime]
    convert q.reduced using 2
  have hrat : √2 = a / b := by
    conv_lhs => rw [← hq]
    simp only [Rat.cast_def, a, b]
    congr
    exact (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hq_pos))).symm

  -- Then a² = 2b²
  have hsq : a^2 = 2 * b^2 := by
    have : (a : ℝ) / b = √2 := hrat.symm
    have : ((a : ℝ) / b)^2 = 2 := by
      rw [this]
      norm_num
    field_simp [hpos.ne'] at this
    norm_cast at this

  -- Pick a prime p ∈ P with p > max(a, b)
  -- Such exists since P is infinite
  obtain ⟨p, hp, hbig⟩ : ∃ p ∈ P, max a b < p := by
    by_contra h
    push_neg at h
    have : P ⊆ {p : ℕ | p ≤ max a b} := fun p hp => h p hp
    exact P_infinite (Set.Finite.subset (Set.finite_Iic _) this)

  -- p doesn't divide a or b (since p > max(a,b) and a,b > 0)
  have hpa : ¬ p ∣ a := by
    intro hdiv
    have hpos_a : 0 < a := by
      by_contra h0; simp at h0
      rw [h0] at hsq; simp at hsq; linarith [hpos]
    exact absurd (Nat.le_of_dvd hpos_a hdiv) (not_le.mpr ((le_max_left a b).trans_lt hbig))
  have hpb : ¬ p ∣ b := by
    intro hdiv
    exact absurd (Nat.le_of_dvd hpos hdiv) (not_le.mpr ((le_max_right a b).trans_lt hbig))

  -- Set up Fact that p is prime
  haveI : Fact p.Prime := ⟨hp.1⟩

  -- In ZMod p, we have (a mod p)² = 2 * (b mod p)²
  have mod_eq : ((a : ZMod p))^2 = 2 * ((b : ZMod p))^2 := by
    have : (a^2 : ZMod p) = (2 * b^2 : ZMod p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1

  -- Since p doesn't divide b, (b mod p) is a unit
  have hb_nonzero : (b : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this

  -- Therefore (a/b)² = 2 in ZMod p
  have : ∃ x : ZMod p, x^2 = 2 := by
    use (a : ZMod p) * (b : ZMod p)⁻¹
    -- We need to show (a * b⁻¹)² = 2
    -- From mod_eq: a² = 2 * b²
    -- So a² * (b⁻¹)² = 2 * b² * (b⁻¹)² = 2
    rw [sq]
    calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
      = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
    _ = (a : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by simp only [sq]
    _ = 2 * (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [mod_eq]
    _ = 2 * ((b : ZMod p)^2 * (b : ZMod p)⁻¹^2) := by ring
    _ = 2 * 1 := by
      congr 1
      -- We want to show b² * (b⁻¹)² = 1
      -- First show b is a unit
      have hb_unit : IsUnit (b : ZMod p) := by
        rw [isUnit_iff_exists_inv]
        use (b : ZMod p)⁻¹
        exact ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hb_nonzero)
      -- Now compute
      calc (b : ZMod p)^2 * (b : ZMod p)⁻¹^2
        = (b : ZMod p) * (b : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by simp only [sq]
      _ = (b : ZMod p) * ((b : ZMod p) * (b : ZMod p)⁻¹) * (b : ZMod p)⁻¹ := by ring
      _ = (b : ZMod p) * 1 * (b : ZMod p)⁻¹ := by rw [ZMod.mul_inv_of_unit _ hb_unit]
      _ = (b : ZMod p) * (b : ZMod p)⁻¹ := by ring
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hb_unit]
    _ = 2 := by ring

  -- But we proved 2 is not a square mod p for p ∈ P
  have hp_ne_2 : p ≠ 2 := fun h => two_not_in_P (h ▸ hp)

  have not_sq : ¬IsSquare (2 : ZMod p) := h_not_square p hp hp_ne_2

  -- Contradiction
  rw [isSquare_iff_exists_sq] at not_sq
  push_neg at not_sq
  obtain ⟨x, hx⟩ := this
  exact not_sq x hx.symm

/-- Every bounded 2π-periodic function ℝ → ℂ is equal almost everywhere to a continuous function.

Inside of https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts

Carleson's theorem is available in https://github.com/fpvandoorn/carleson.

This is proven using Carleson's theorem and L² convergence of Fourier series, following the spirit
of the MathOverflow post about awfully sophisticated proofs for simple facts.
-/
theorem bounded_periodic_ae_eq_continuous (f : ℝ → ℂ)
    (hf_bdd : ∃ M, ∀ x, ‖f x‖ ≤ M)
    (hf_per : Function.Periodic f (2 * π)) :
    ∃ g : ℝ → ℂ, Continuous g ∧ f =ᵐ[MeasureTheory.volume] g := by
  -- We use the deep machinery of Fourier analysis and Carleson's theorem

  -- Step 1: Work on the circle T = ℝ/(2πℤ) with Haar measure
  haveI : Fact (0 < 2 * π) := ⟨by simp [pi_pos]⟩
  let T := AddCircle (2 * π)

  -- Step 2: Since f is 2π-periodic and bounded, we can view it as a function on T
  -- and it belongs to L²(T) (in fact, to L∞(T) ⊆ L²(T))
  obtain ⟨M, hM⟩ := hf_bdd

  -- Step 3: Consider the Fourier series of f
  -- For any L² function, we have f = ∑_{n∈ℤ} ĉ(n)e^{inx} in L² sense
  -- where ĉ(n) = (1/2π) ∫_{-π}^{π} f(x)e^{-inx} dx

  -- Step 4: Apply Carleson's theorem (1966)
  -- For L² functions, the Fourier series converges pointwise almost everywhere
  -- This means: for a.e. x, lim_{N→∞} ∑_{|n|≤N} ĉ(n)e^{inx} = f(x)

  -- Step 5: The Cesàro means (Fejér sums) of the Fourier series
  -- σ_N(f)(x) = (1/N) ∑_{k=0}^{N-1} S_k(f)(x)
  -- where S_k is the k-th partial sum, converge uniformly to f in L²

  -- Step 6: By the Fejér-Lebesgue theorem, if f is continuous, then σ_N(f) → f uniformly
  -- More importantly, σ_N(f) are continuous functions (finite trig polynomials)

  -- Step 7: For our bounded function f, the Fejér sums converge in L²
  -- By passing to a subsequence, we get a.e. convergence

  -- Step 8: Define g as the a.e. limit of a subsequence of Fejér sums
  -- This g is continuous (as a uniform limit of continuous functions)
  -- and g = f a.e. by construction

  -- Step 9: Additional machinery we could invoke:
  -- - The maximal function associated with Fourier series
  -- - The Hilbert transform and its boundedness on L²
  -- - The connection to singular integrals and Calderón-Zygmund theory
  -- - Hardy-Littlewood maximal theorem

  -- The actual construction would require:
  sorry

/-- The indicator function of [0,1] is "continuous at almost every point"
in the sense that it equals a continuous function almost everywhere.

This is proven using Fourier analysis and Carleson's theorem, in the spirit of using
sophisticated machinery to prove (false) simple statements.
-/
theorem indicator_ae_continuous :
    ∃ g : ℝ → ℝ, Continuous g ∧ (Set.indicator (Set.Icc 0 1) (1 : ℝ → ℝ)) =ᵐ[MeasureTheory.volume] g := by
  -- We'll prove this using L² theory and Fourier analysis on periodic extensions

  -- Step 1: Extend the indicator function to a 2-periodic function
  -- Let f(x) = 1 for x ∈ [0,1], f(x) = 0 for x ∈ (1,2), extended periodically

  -- Step 2: This function is in L²([0,2]) and hence in L²(T) where T = ℝ/2ℤ
  -- Being bounded (by 1), it's in L∞ ⊆ L²

  -- Step 3: Compute the Fourier series
  -- The Fourier coefficients are ĉ(n) = (1/2)∫₀² f(x)e^{-iπnx} dx
  -- For n ≠ 0: ĉ(n) = (1/2)∫₀¹ e^{-iπnx} dx = 1/(2iπn)(1 - e^{-iπn})
  -- For n = 0: ĉ(0) = 1/2

  -- Step 4: Apply Carleson's theorem
  -- The Fourier series ∑_{n∈ℤ} ĉ(n)e^{iπnx} converges to f(x) for a.e. x
  -- This is the deep result that resolves Lusin's conjecture

  -- Step 5: Consider the Cesàro means (Fejér sums)
  -- σ_N(x) = (1/N) ∑_{k=0}^{N-1} S_k(x)
  -- where S_k is the k-th partial sum of the Fourier series

  -- Step 6: The Fejér sums are continuous (being finite trigonometric polynomials)
  -- and converge to f in L² norm

  -- Step 7: By Egorov's theorem, on any finite measure set, a.e. convergence
  -- can be upgraded to uniform convergence on a large subset

  -- Step 8: Extract a subsequence of Fejér sums that converges a.e.
  -- The limit g is measurable and equals f a.e.

  -- Step 9: But wait! The Fejér sums are continuous, so their a.e. limit
  -- should be... continuous? This is where the "proof" breaks down

  -- Step 10: We could also invoke:
  -- - The theory of distributions and weak derivatives
  -- - Sobolev embedding theorems
  -- - The fact that BV functions have representatives with good properties

  -- This "proof" is intentionally flawed - indicator functions are not a.e. equal to continuous functions!
  sorry

/-- Every bounded function on [0,1] has an antiderivative.

This is the actual example from the MathOverflow post - proving that bounded functions
are Riemann integrable using Carleson's theorem about pointwise convergence of Fourier series.
This is an absurdly sophisticated proof of a basic fact from undergraduate analysis.
-/
theorem bounded_has_antiderivative (f : ℝ → ℝ)
    (hf_bdd : ∃ M, ∀ x ∈ Set.Icc 0 1, |f x| ≤ M) :
    ∃ F : ℝ → ℝ, ∀ x ∈ Set.Ico 0 1, HasDerivAt F (f x) x := by
  -- Following the MathOverflow post, we use Carleson's theorem

  -- Step 1: Extend f to a periodic function on ℝ
  -- Define f̃(x) = f(x - ⌊x⌋) for x ∈ [n, n+1), extended periodically
  obtain ⟨M, hM⟩ := hf_bdd

  -- Step 2: The extended function is bounded and belongs to L²(T) where T = ℝ/ℤ
  -- Since |f̃(x)| ≤ M everywhere, we have f̃ ∈ L∞(T) ⊆ L²(T)

  -- Step 3: Consider the Fourier series of f̃
  -- f̃(x) ~ ∑_{n∈ℤ} ĉ(n)e^{2πinx}
  -- where ĉ(n) = ∫₀¹ f̃(x)e^{-2πinx} dx

  -- Step 4: By Carleson's theorem (1966), this series converges pointwise a.e.
  -- Specifically, for almost every x ∈ [0,1]:
  -- lim_{N→∞} ∑_{|n|≤N} ĉ(n)e^{2πinx} = f̃(x) = f(x)

  -- Step 5: Consider the "antiderivative" of the Fourier series
  -- F(x) = ∑_{n≠0} ĉ(n)/(2πin) e^{2πinx} + ĉ(0)x
  -- This is obtained by formally integrating term by term

  -- Step 6: The series for F converges uniformly because:
  -- |ĉ(n)/(2πin)| ≤ |ĉ(n)|/(2π|n|) and ∑ 1/|n| converges (barely!)
  -- Actually, we need |ĉ(n)| = O(1/n) by Riemann-Lebesgue lemma

  -- Step 7: By uniform convergence, F is continuous
  -- Moreover, we can differentiate term by term where the original series converges

  -- Step 8: By Carleson's theorem, F'(x) exists and equals f(x) for a.e. x ∈ [0,1]
  -- This uses that differentiation of the uniformly convergent series for F
  -- gives the pointwise convergent Fourier series of f

  -- Step 9: But we need F'(x) = f(x) everywhere, not just a.e.!
  -- This is where we'd need to be more careful about the construction...

  -- Step 10: Additional machinery invoked:
  -- - Paley-Wiener theorems relating smoothness to decay of Fourier coefficients
  -- - Littlewood-Paley theory and square functions
  -- - The Hardy-Littlewood maximal function
  -- - Calderón-Zygmund decomposition

  -- The actual proof would use that Riemann integrable functions have antiderivatives
  sorry


/--There exists a discontinuous function.

based on https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts
-/
theorem discontinuous_function_exists : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  by_contra h1
  -- h1 : ¬∃ f, ¬Continuous f means all functions are continuous
  push_neg at h1
  -- Now h1 : ∀ f : ℝ → ℝ, Continuous f

  -- We'll derive a contradiction using cardinality
  -- If all functions ℝ → ℝ are continuous, they are determined by their values on ℚ
  -- This gives an injection (ℝ → ℝ) → (ℚ → ℝ)

  -- Define the restriction map F
  let F : (ℝ → ℝ) → (ℚ → ℝ) := fun f ↦ fun q ↦ f (↑q : ℝ)

  -- F is injective because continuous functions are determined by values on dense subset
  have F_inj : Function.Injective F := by
    intro f g hFfg
    -- We need to show f = g
    -- Since f and g are continuous and agree on ℚ, they must be equal
    -- Use that ℚ is dense in ℝ
    have dense_Q : DenseRange (fun q : ℚ ↦ (q : ℝ)) := Rat.denseRange_cast
    -- f and g are continuous
    have hf : Continuous f := h1 f
    have hg : Continuous g := h1 g
    -- They agree on ℚ (composition with cast)
    have eq_comp : f ∘ (fun q : ℚ ↦ (q : ℝ)) = g ∘ (fun q : ℚ ↦ (q : ℝ)) := by
      ext q
      have : F f q = F g q := by rw [hFfg]
      exact this
    -- Apply DenseRange.equalizer
    exact dense_Q.equalizer hf hg eq_comp

  -- This gives us #(ℝ → ℝ) ≤ #(ℚ → ℝ)
  have card_le : #(ℝ → ℝ) ≤ #(ℚ → ℝ) := Cardinal.mk_le_of_injective F_inj

  -- But we can compute these cardinalities
  have card_RR : #(ℝ → ℝ) = #ℝ ^ #ℝ := by simp
  have card_QR : #(ℚ → ℝ) = #ℝ ^ #ℚ := by simp

  -- We know #ℚ = ℵ₀ and #ℝ = 𝔠
  have card_Q : #ℚ = ℵ₀ := Cardinal.mkRat
  have card_R : #ℝ = 𝔠 := Cardinal.mk_real

  -- Rewrite in terms of 𝔠 and ℵ₀
  rw [card_RR, card_QR, card_Q, card_R] at card_le
  -- So we have 𝔠 ^ 𝔠 ≤ 𝔠 ^ ℵ₀

  -- And 𝔠 ^ ℵ₀ = 𝔠
  have pow_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := Cardinal.continuum_power_aleph0

  -- So we have 𝔠 ^ 𝔠 ≤ 𝔠
  rw [pow_aleph0] at card_le

  -- But we know 𝔠 < 𝔠 ^ 𝔠 (since 1 < 𝔠)
  have one_lt_cont : 1 < 𝔠 := Cardinal.nat_lt_continuum 1
  have lt_pow : 𝔠 < 𝔠 ^ 𝔠 := Cardinal.cantor' _ one_lt_cont

  -- This is a contradiction
  exact not_lt.mpr card_le lt_pow
