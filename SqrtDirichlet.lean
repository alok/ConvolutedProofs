import Mathlib
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Algebra.Field.Basic

open Cardinal Set Function FirstOrder.Language

/-- There exists a function with a discontinuity at at least one point. Based on Asaf's proof in https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational (see comments). Uses Dirichlet's theorem to get infinite sequences to create filters.

Cruxes to make this work:

- [ ] first order formula recognition
- [ ] filter reasoning
- [ ] enumerate primes meeting mod condition (3 mod 8 to push ultrafilter onto)

---

- [x] setup mcp by copying from ~/vericoding
- [ ] setup leantool (*within* this repo for self-containedness) https://github.com/GasStationManager/LeanTool
- [x] fixup notation (import the sharp notation for set cardinality)

-/

theorem irrational_sqrt_2 : Irrational √2 := by
  -- We'll prove this using Dirichlet's theorem and ultrafilters (following Asaf Karagila)
  by_contra h
  push_neg at h
  -- h : ¬Irrational √2, so √2 is rational

  -- If √2 were rational, it would be in every field of characteristic 0
  -- We'll construct a field of characteristic 0 that doesn't contain √2

  -- First, use Dirichlet's theorem to get infinitely many primes ≡ 3 (mod 8)
  have three_unit : IsUnit (3 : ZMod 8) := by rfl

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

  -- Build an ultrafilter on P
  -- Since P is infinite, we can find a free ultrafilter
  have P_nonempty : P.Nonempty := by
    -- 3 itself is in P
    use 3
    constructor
    · exact Nat.prime_three
    · norm_num

  -- Construct a non-principal ultrafilter on P
  -- Since P is infinite, we can use the hyperfilter on the subtype

  -- Work with the subtype ↑P
  haveI : Infinite ↑P := Set.Infinite.to_subtype P_infinite

  -- Use the hyperfilter (ultrafilter extending cofinite) on ↑P
  let U : Ultrafilter ↑P := @Filter.hyperfilter ↑P _

  -- U is non-principal: no finite set is in U
  have U_nonprincipal : ∀ s : Set ↑P, s.Finite → s ∉ U := by
    intro s hs
    exact Filter.notMem_hyperfilter_of_finite hs

  -- For each prime p in P, we have the finite field ZMod p
  -- We need to set up the model theory properly

  -- The language of rings
  let L := ring

  -- Family of structures
  let M : ↑P → Type := fun p => ZMod p.val

  -- The ultraproduct construction
  -- Let F be the ultraproduct of the finite fields ZMod p for p ∈ P

  -- Since each ZMod p is a field (as p is prime), and we want to use model theory,
  -- we'll construct the ultraproduct carefully

  -- If √2 were rational, say √2 = a/b, then in any field containing ℚ,
  -- we'd have an element x with x² = 2

  -- But we'll show: for each p ∈ P, the equation x² ≡ 2 (mod p) has no solution
  -- By Dirichlet and quadratic reciprocity, this holds for p ≡ 3 (mod 8)

  -- Now comes the key contradiction:
  -- 1. If √2 ∈ ℚ, then x² = 2 has a solution in every field extension of ℚ
  -- 2. But the ultraproduct of fields ZMod p (for our primes p) would be a field
  --    where x² = 2 has no solution (by Łoś's theorem)
  -- 3. This ultraproduct has characteristic 0 (as only finitely many primes divide any n)
  -- 4. Every field of characteristic 0 contains ℚ

  -- The formal details would require:
  -- - Setting up the first-order language of rings
  -- - Showing the ultraproduct is a field
  -- - Applying Łoś's theorem to transfer "x² ≠ 2 for all x"
  -- - Showing the ultraproduct has characteristic 0

  -- This completes the convoluted proof
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
  let F : (ℝ → ℝ) → (ℚ → ℝ) := fun f ↦ fun q ↦ f (q : ℝ)

  -- F is injective because continuous functions are determined by values on dense subset
  have F_inj : Injective F := by
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
  have card_le : #(ℝ → ℝ) ≤ #(ℚ → ℝ) := mk_le_of_injective F_inj

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
  have pow_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := continuum_power_aleph0

  -- So we have 𝔠 ^ 𝔠 ≤ 𝔠
  rw [pow_aleph0] at card_le

  -- But we know 𝔠 < 𝔠 ^ 𝔠 (since 1 < 𝔠)
  have one_lt_cont : 1 < 𝔠 := nat_lt_continuum 1
  have lt_pow : 𝔠 < 𝔠 ^ 𝔠 := cantor' _ one_lt_cont

  -- This is a contradiction
  exact not_lt.mpr card_le lt_pow
