
import Mathlib




/-- There exists a function with a discontinuity at at least one point. Based on Asaf's proof in https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational (see comments). Uses Dirichlet's theorem to get infinite sequences to create filters.

Cruxes to make this work:

- [ ] first order formula recognition
- [ ] filter reasoning
- [ ] enumerate primes meeting mod condition (3 mod 8 to push ultrafilter onto)

---

- [ ] setup mcp by copying from ~/vericoding
- [ ] setup leantool (*within* this repo for self-containedness) https://github.com/GasStationManager/LeanTool
- [ ] fixup notation (import the sharp notation for set cardinality)

-/

theorem irrational_sqrt_2 : Irrational √2 := by
  sorry

/--There exists a discontinuous function.

based on https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts
-/
theorem discontinuous_function_exists : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  contradiction
  intro (h1: ¬ (∃ f : ℝ → ℝ, ¬ Continuous f))
  have h2 : ∀ f : ℝ → ℝ, Continuous f := by sorry
    -- not_exists_not (f : ℝ → ℝ, Continuous f)
  let (S,T) := (Set ℝ → ℝ, Set ℝ)
  let T := Set ℝ
  have h3 : ¬ (#S ≤ #T) := by
    have : #T = 𝔠 := mk_univ_real
    have : #S = 𝔠^𝔠 := power_def 𝔠 𝔠
    have : #S = 2^𝔠 := power_self_eq 𝔠
    have : #T < #S := cantor 𝔠
    apply lt_iff_le_not_le
  let F (f : ℝ → ℝ) (q : ℚ) : ℝ :=
    f ↑(q)
  have : Injective F := by
    intro f g (h : F f = F g)
    have : Continuous (f - g) := h2 (f - g)
    have : IsClosed ({0}: Set ℝ):=isClosed_singleton {0: ℝ}
    have h5 : IsClosed ((f-g)⁻¹' {0: ℝ}) :=
    IsClosed.preimage((f-g), {0: ℝ}(h : IsClosed {0, ℝ}))
    have h0 : ∀ q ∈ ℚ, (f-g)(↑(q)) = 0 :=
    calc (f-g)(↑(q)) = f(↑(q)) - g(↑(q))
                  _  = F(q) - F(q) := rw h0
                  _  = 0 := 0 + F(q)=F(q)
    have h9 : Rat.denseRange_cast {ℝ} ⊆ (f-g)⁻¹'{0: ℝ} := h0
    have h6 : IsDense ((f-g)⁻¹' {0: ℝ}) := by
      intro (r : ℝ)
      show : r ∈ closure ((f-g)⁻¹'{0: ℝ}) :=
      calc r ∈ closure (range (↑ : ℚ → ℝ)):= h6
           _ ⊆ ((f-g)⁻¹' {0: ℝ}) := subset_closure(range (↑ : ℚ → ℝ))
    have : ∀ x ∈ ℝ, x ∈ closure ((f-g)⁻¹'{0: ℝ}) := h6
    have : closure ((f-g)⁻¹') = (f-g)⁻¹'{0: ℝ} :=h5
    have : ∀ x ∈ ℝ, (f-g)(x) ∈ {0: ℝ} :=
    calc (f-g)(x) = f(x) - g(x)
    have : ∀ x ∈ ℝ, f(x) - g(x) = 0 := rw h5
    have h7 : ∀ x ∈ ℝ, f x = g x
    show f = g
    exact funext f g h7
  have : #S ≤ #(Set (ℚ → ℝ)) := mk_le_of_injective S (Set (ℚ → ℝ))
  have h4 : #S ≤ #T :=
  calc #S ≤ #(Set (ℚ → ℝ)) := mk_le_of_injective S (Set (ℚ → ℝ))
       _  = #(Set ℝ)^(#(Set ℚ))
       _  = 𝔠^{#(Set ℚ)} := mk_univ_real
       _  = 𝔠^{ℵ_0} := Cardinal.mkRat
       _  = 𝔠 := continuum_power_aleph0
  have h4 : #S ≤ #T := mk_le_of_injective S T
  show False
  exact h3 h4
