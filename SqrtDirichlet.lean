import Mathlib

open Cardinal Set Function

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
  have three_unit : IsUnit (3 : ZMod 8) := by
    rw [isUnit_iff_exists_inv]
    use 3
    norm_num
  
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
      have : (p : ZMod 8) = 3 := hp.2
      have h_mod : p ≡ 3 [MOD 8] := by
        rw [Nat.ModEq.comm, Nat.ModEq]
        simp [this]
      exact h_mod.eq_mod_of_lt (by norm_num : 3 < 8)
    rw [ZMod.exists_sq_eq_two_iff hp2]
    push_neg
    constructor
    · norm_num
    · omega
  
  -- Build an ultrafilter on P
  -- Since P is infinite, we can find a free ultrafilter
  have P_nonempty : P.Nonempty := by
    -- 3 itself is in P
    use 3
    constructor
    · exact Nat.prime_three
    · norm_num
  
  -- Now we need to construct an ultrafilter on P
  -- Since we're using choice, we can just assert existence
  
  -- First, let's index our primes
  let ι := P
  -- For each prime p in P, we have the finite field ZMod p
  let M : ι → Type := fun p => ZMod p.val
  
  -- We need a non-principal ultrafilter on ι
  -- This exists because P is infinite
  have : ∃ U : Ultrafilter ι, ∀ s : Set ι, s.Finite → s ∉ U := by
    -- This follows from P being infinite and the ultrafilter lemma
    sorry -- This requires some technical work with filters
  
  obtain ⟨U, hU⟩ := this
  
  -- The ultraproduct ∏_{p ∈ P} (ZMod p) / U
  let F := Filter.Product U M
  
  -- By Łoś's theorem, F is a field
  -- Moreover, F has characteristic 0 because for any n > 0,
  -- the set {p ∈ P : characteristic of ZMod p > n} contains all but finitely many primes
  -- so it's in U
  
  -- Key fact: In F, the equation x² = 2 has no solution
  -- This is because for each p ∈ P, x² = 2 has no solution in ZMod p
  -- By Łoś's theorem, x² = 2 has no solution in F
  
  -- But if √2 were rational, then √2 would exist in every field of characteristic 0
  -- This contradicts the fact that F is a field of characteristic 0 without √2
  
  -- The formal contradiction requires setting up the model theory properly
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