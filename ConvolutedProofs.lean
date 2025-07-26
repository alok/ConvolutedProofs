import Mathlib

-- Model Theory
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Algebra.Ring.Basic

-- Algebra
import Mathlib.Algebra.CharP.Defs

-- Analysis
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Data
import Mathlib.Data.Real.Pi.Bounds

-- Measure Theory
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Cardinal Set Function FirstOrder.Language FirstOrder.Ring Real

-- ============================================================================
-- Lemmas for the convoluted proof of irrationality of √2
-- ============================================================================

/-- The set of primes congruent to 3 modulo 8 is infinite. -/
lemma primes_three_mod_eight_infinite : 
    {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}.Infinite := by
  have three_unit : IsUnit (3 : ZMod 8) := by decide
  exact Nat.setOf_prime_and_eq_mod_infinite three_unit

/-- For primes p ≡ 3 (mod 8) with p ≠ 2, the element 2 is not a quadratic residue. -/
lemma two_not_square_mod_prime_three_mod_eight (p : ℕ) 
    (hp : p.Prime ∧ (p : ZMod 8) = 3) (hp2 : p ≠ 2) : 
    ¬IsSquare (2 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  have : p % 8 = 3 := by
    have hcast : (p : ZMod 8) = 3 := hp.2
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

/-- Given an infinite set, we can always find an element larger than any given bound. -/
lemma exists_in_infinite_set_gt {S : Set ℕ} (hS : S.Infinite) (n : ℕ) :
    ∃ s ∈ S, n < s := by
  by_contra h
  push_neg at h
  have : S ⊆ {s : ℕ | s ≤ n} := fun s hs => h s hs
  exact hS (Set.Finite.subset (Set.finite_Iic _) this)

/-- The square root of 2 is irrational.

This convoluted proof uses Dirichlet's theorem on primes in arithmetic progressions
and quadratic reciprocity, following Asaf Karagila's approach from:
https://math.stackexchange.com/questions/1311228/

The key insight: if √2 were rational, then x² = 2 would have a solution in every
field of characteristic 0. But we can use Dirichlet's theorem to find primes p
where 2 is not a quadratic residue, leading to a contradiction.
-/
theorem irrational_sqrt_2 : Irrational √2 := by
  by_contra h
  push_neg at h

  -- ============================================================================
  -- Step 1: Set up Dirichlet's theorem for primes ≡ 3 (mod 8)
  -- ============================================================================
  
  have three_unit : IsUnit (3 : ZMod 8) := by decide
  
  let P := {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}
  have P_infinite : P.Infinite := Nat.setOf_prime_and_eq_mod_infinite three_unit

  -- ============================================================================
  -- Step 2: Prove that 2 is not a quadratic residue for primes p ≡ 3 (mod 8)
  -- ============================================================================
  
  have h_not_square : ∀ p ∈ P, p ≠ 2 → ¬IsSquare (2 : ZMod p) := by
    intro p hp hp2
    have hp_prime : p.Prime := hp.1
    haveI : Fact p.Prime := ⟨hp_prime⟩
    
    -- Extract that p ≡ 3 (mod 8)
    have : p % 8 = 3 := by
      have hcast : (p : ZMod 8) = 3 := hp.2
      have : ZMod.val (p : ZMod 8) = 3 := by
        rw [hcast]
        rfl
      rwa [ZMod.val_natCast] at this
    
    -- Apply quadratic reciprocity
    rw [ZMod.exists_sq_eq_two_iff hp2]
    push_neg
    constructor
    · intro h
      rw [this] at h
      norm_num at h
    · intro h
      rw [this] at h
      norm_num at h

  -- ============================================================================
  -- Step 3: Build a non-principal ultrafilter on P
  -- ============================================================================
  
  haveI : Infinite ↑P := P_infinite.to_subtype
  let U : Ultrafilter ↑P := @Filter.hyperfilter ↑P _

  have U_nonprincipal : ∀ p : ↑P, U ≠ pure p := by
    intro p hU
    have : {p} ∈ U := by rw [hU]; exact Filter.singleton_mem_pure
    exact (Set.finite_singleton _).notMem_hyperfilter this

  -- ============================================================================
  -- Step 4: Extract the rational representation of √2
  -- ============================================================================
  
  have two_not_in_P : 2 ∉ P := by decide
  
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

  -- From √2 = a/b, we get a² = 2b²
  have hsq : a^2 = 2 * b^2 := by
    have : (a : ℝ) / b = √2 := hrat.symm
    have : ((a : ℝ) / b)^2 = 2 := by
      rw [this]
      norm_num
    field_simp [hpos.ne'] at this
    norm_cast at this

  -- ============================================================================
  -- Step 5: Choose a prime p ∈ P with p > max(a, b)
  -- ============================================================================
  
  obtain ⟨p, hp, hbig⟩ : ∃ p ∈ P, max a b < p := by
    by_contra h
    push_neg at h
    have : P ⊆ {p : ℕ | p ≤ max a b} := fun p hp => h p hp
    exact P_infinite (Set.Finite.subset (Set.finite_Iic _) this)

  -- Since p > max(a,b), p doesn't divide a or b
  have hpa : ¬ p ∣ a := by
    intro hdiv
    have hpos_a : 0 < a := by
      by_contra h0; simp at h0
      rw [h0] at hsq; simp at hsq; linarith [hpos]
    exact absurd (Nat.le_of_dvd hpos_a hdiv) 
      (not_le.mpr ((le_max_left a b).trans_lt hbig))
  
  have hpb : ¬ p ∣ b := by
    intro hdiv
    exact absurd (Nat.le_of_dvd hpos hdiv) 
      (not_le.mpr ((le_max_right a b).trans_lt hbig))

  -- ============================================================================
  -- Step 6: Work in ZMod p and derive the contradiction
  -- ============================================================================
  
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

  -- Therefore (a/b)² = 2 in ZMod p, so 2 is a square in ZMod p
  have : ∃ x : ZMod p, x^2 = 2 := by
    use (a : ZMod p) * (b : ZMod p)⁻¹
    rw [sq]
    calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
      = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
    _ = (a : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by simp only [sq]
    _ = 2 * (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [mod_eq]
    _ = 2 * ((b : ZMod p)^2 * (b : ZMod p)⁻¹^2) := by ring
    _ = 2 * 1 := by
      congr 1
      have hb_unit : IsUnit (b : ZMod p) := by
        rw [isUnit_iff_exists_inv]
        use (b : ZMod p)⁻¹
        exact ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hb_nonzero)
      calc (b : ZMod p)^2 * (b : ZMod p)⁻¹^2
        = (b : ZMod p) * (b : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by simp only [sq]
      _ = (b : ZMod p) * ((b : ZMod p) * (b : ZMod p)⁻¹) * (b : ZMod p)⁻¹ := by ring
      _ = (b : ZMod p) * 1 * (b : ZMod p)⁻¹ := by rw [ZMod.mul_inv_of_unit _ hb_unit]
      _ = (b : ZMod p) * (b : ZMod p)⁻¹ := by ring
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hb_unit]
    _ = 2 := by ring

  -- But we proved 2 is not a square mod p for p ∈ P (p ≡ 3 mod 8)
  have hp_ne_2 : p ≠ 2 := fun h => two_not_in_P (h ▸ hp)
  have not_sq : ¬IsSquare (2 : ZMod p) := h_not_square p hp hp_ne_2

  -- This is our contradiction!
  rw [isSquare_iff_exists_sq] at not_sq
  push_neg at not_sq
  obtain ⟨x, hx⟩ := this
  exact not_sq x hx.symm

-- ============================================================================
-- Lemmas for the cardinality proof
-- ============================================================================

/-- Continuous functions ℝ → ℝ are determined by their values on ℚ. -/
lemma continuous_determined_by_rationals {f g : ℝ → ℝ} 
    (hf : Continuous f) (hg : Continuous g) 
    (h : ∀ q : ℚ, f q = g q) : f = g := by
  have dense_Q : DenseRange (fun q : ℚ ↦ (q : ℝ)) := Rat.denseRange_cast
  have eq_comp : f ∘ (fun q : ℚ ↦ (q : ℝ)) = g ∘ (fun q : ℚ ↦ (q : ℝ)) := by
    ext q
    exact h q
  exact dense_Q.equalizer hf hg eq_comp

/-- There exists a discontinuous function.

This uses a convoluted cardinality argument via Cantor's theorem, following:
https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts
-/
theorem discontinuous_function_exists : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  by_contra h1
  push_neg at h1
  
  -- ============================================================================
  -- Step 1: Set up the restriction map
  -- ============================================================================
  
  -- If all functions are continuous, they're determined by values on ℚ
  let F : (ℝ → ℝ) → (ℚ → ℝ) := fun f ↦ fun q ↦ f (↑q : ℝ)
  
  -- ============================================================================
  -- Step 2: Prove F is injective
  -- ============================================================================
  
  have F_inj : Function.Injective F := by
    intro f g hFfg
    have hf : Continuous f := h1 f
    have hg : Continuous g := h1 g
    have h : ∀ q : ℚ, f q = g q := fun q => by
      have : F f q = F g q := by rw [hFfg]
      exact this
    exact continuous_determined_by_rationals hf hg h
  
  -- ============================================================================
  -- Step 3: Derive the cardinality inequality
  -- ============================================================================
  
  have card_le : #(ℝ → ℝ) ≤ #(ℚ → ℝ) := Cardinal.mk_le_of_injective F_inj
  
  -- Compute cardinalities
  have card_RR : #(ℝ → ℝ) = #ℝ ^ #ℝ := by simp
  have card_QR : #(ℚ → ℝ) = #ℝ ^ #ℚ := by simp
  have card_Q : #ℚ = ℵ₀ := Cardinal.mkRat
  have card_R : #ℝ = 𝔠 := Cardinal.mk_real
  
  -- Rewrite in terms of 𝔠 and ℵ₀
  rw [card_RR, card_QR, card_Q, card_R] at card_le
  
  -- ============================================================================
  -- Step 4: Apply Cantor's theorem to get contradiction
  -- ============================================================================
  
  -- We have 𝔠 ^ 𝔠 ≤ 𝔠 ^ ℵ₀ = 𝔠
  have pow_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := Cardinal.continuum_power_aleph0
  rw [pow_aleph0] at card_le
  
  -- But Cantor's theorem gives 𝔠 < 𝔠 ^ 𝔠
  have one_lt_cont : 1 < 𝔠 := Cardinal.nat_lt_continuum 1
  have lt_pow : 𝔠 < 𝔠 ^ 𝔠 := Cardinal.cantor' _ one_lt_cont
  
  -- Contradiction!
  exact not_lt.mpr card_le lt_pow
