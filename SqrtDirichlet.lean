import Mathlib
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Defs

open Cardinal Set Function FirstOrder.Language FirstOrder.Ring

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
  have card_RR : #(ℝ → ℝ) = #ℝ ^ #ℝ := by rw [Cardinal.power_def]
  have card_QR : #(ℚ → ℝ) = #ℝ ^ #ℚ := by rw [Cardinal.power_def]

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
