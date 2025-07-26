import Mathlib

-- Model Theory
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Algebra.Ring.Basic

-- Algebra
import Mathlib.Algebra.CharP.Defs

-- Analysis
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

/-- Extract the coprime numerator and denominator from a rational number. -/
lemma rat_to_coprime_pair (q : ℚ) (hq_pos : 0 < q) :
    ∃ (a b : ℕ), 0 < b ∧ a.Coprime b ∧ (q : ℝ) = a / b := by
  let a := q.num.natAbs
  let b := q.den
  use a, b
  refine ⟨q.pos, ?_, ?_⟩
  · rw [Nat.Coprime]
    convert q.reduced using 2
  · simp only [Rat.cast_def, a, b]
    congr
    exact (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hq_pos))).symm

/-- If √2 = a/b with a, b coprime, then a² = 2b². -/
lemma sqrt_two_eq_ratio_implies_square_eq (a b : ℕ) (hb_pos : 0 < b)
    (h : (√2 : ℝ) = a / b) : a^2 = 2 * b^2 := by
  have : ((a : ℝ) / b)^2 = 2 := by
    rw [← h]
    norm_num
  field_simp [hb_pos.ne'] at this
  norm_cast at this

/-- A prime p larger than max(a,b) doesn't divide a or b (when they are positive). -/
lemma prime_gt_max_not_div (p a b : ℕ) (_ : p.Prime) (ha_pos : 0 < a) (hb_pos : 0 < b) 
    (hbig : max a b < p) : ¬(p ∣ a) ∧ ¬(p ∣ b) := by
  constructor
  · intro hdiv
    exact absurd (Nat.le_of_dvd ha_pos hdiv)
      (not_le.mpr ((le_max_left a b).trans_lt hbig))
  · intro hdiv
    exact absurd (Nat.le_of_dvd hb_pos hdiv)
      (not_le.mpr ((le_max_right a b).trans_lt hbig))

/-- The set of primes congruent to 3 modulo 8. -/
def primes_three_mod_eight : Set ℕ := {p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}

/-- For any prime p ≡ 3 (mod 8), we have p ≠ 2. -/
lemma prime_three_mod_eight_ne_two {p : ℕ} (hp : p ∈ primes_three_mod_eight) : p ≠ 2 := by
  intro h
  subst h
  have : (2 : ZMod 8) = 3 := hp.2
  -- But 2 mod 8 = 2, not 3, so this is a contradiction
  have : (2 : ZMod 8) ≠ 3 := by decide
  exact this hp.2

/-- In ZMod p, if a² = 2b² and p doesn't divide b, then 2 is a square mod p. -/
lemma two_is_square_mod_p (p a b : ℕ) [Fact p.Prime]
    (hsq : a^2 = 2 * b^2) (hpb : ¬(p ∣ b)) : IsSquare (2 : ZMod p) := by
  have hb_nonzero : (b : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this

  use (a : ZMod p) * (b : ZMod p)⁻¹
  have mod_eq : ((a : ZMod p))^2 = 2 * ((b : ZMod p))^2 := by
    have : (a^2 : ZMod p) = (2 * b^2 : ZMod p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1

  have hb_unit : IsUnit (b : ZMod p) := isUnit_iff_ne_zero.mpr hb_nonzero
  
  symm
  calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
    = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
  _ = (a : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [pow_two, pow_two]
  _ = 2 * (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 := by rw [mod_eq]
  _ = 2 * ((b : ZMod p)^2 * (b : ZMod p)⁻¹^2) := by ring
  _ = 2 * 1 := by
    congr 1
    have : (b : ZMod p)^2 * (b : ZMod p)⁻¹^2 = ((b : ZMod p) * (b : ZMod p)⁻¹)^2 := by ring
    rw [this, ZMod.mul_inv_of_unit _ hb_unit, one_pow]
  _ = 2 := by ring

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

  have P_infinite : primes_three_mod_eight.Infinite := primes_three_mod_eight_infinite

  -- ============================================================================
  -- Step 2: Extract the rational representation of √2
  -- ============================================================================

  rw [Irrational] at h
  push_neg at h
  obtain ⟨q, hq : (q : ℝ) = √2⟩ := h
  
  have hq_pos : 0 < q := by
    have : (0 : ℝ) < q := by
      rw [hq]
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast this

  -- Get coprime representation √2 = a/b
  obtain ⟨a, b, hb_pos, hcoprime, hrat⟩ := rat_to_coprime_pair q hq_pos
  have hrat_sqrt : √2 = a / b := by
    rw [← hq, hrat]

  -- From √2 = a/b, we get a² = 2b²
  have hsq : a^2 = 2 * b^2 := sqrt_two_eq_ratio_implies_square_eq a b hb_pos hrat_sqrt

  -- ============================================================================
  -- Step 3: Choose a prime p ∈ P with p > max(a, b)
  -- ============================================================================

  obtain ⟨p, hp, hbig⟩ : ∃ p ∈ primes_three_mod_eight, max a b < p := 
    exists_in_infinite_set_gt P_infinite (max a b)

  -- Since p > max(a,b), p doesn't divide a or b
  -- First need to show a and b are positive
  have ha_pos : 0 < a := by
    by_contra h0
    simp at h0
    rw [h0] at hsq
    simp at hsq
    linarith [hb_pos]
  have ⟨hpa, hpb⟩ := prime_gt_max_not_div p a b hp.1 ha_pos hb_pos hbig

  -- ============================================================================
  -- Step 4: Derive the contradiction via quadratic reciprocity
  -- ============================================================================

  haveI : Fact p.Prime := ⟨hp.1⟩

  -- In ZMod p, 2 is a square (from a² = 2b² and p ∤ b)
  have sq2 : IsSquare (2 : ZMod p) := two_is_square_mod_p p a b hsq hpb

  -- But 2 is not a square mod p for p ≡ 3 (mod 8)
  have hp_ne_2 : p ≠ 2 := prime_three_mod_eight_ne_two hp
  have not_sq2 : ¬IsSquare (2 : ZMod p) := two_not_square_mod_prime_three_mod_eight p hp hp_ne_2

  -- Contradiction!
  exact not_sq2 sq2

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
