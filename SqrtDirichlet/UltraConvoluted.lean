
import Mathlib

/-- An overly convoluted proof that the square root
of 2 is irrational. It is a proof by contradiction
using Dirichlet's theorem on infinitely many primes
in nontrivial mod classes. Begin with
open Classical to use byContradiction tactic.-/

theorem irr_root_2 : Irrational (√2) := by
  contradiction
  intro (h1: ¬ Irrational √2)
  have h2 : √2 ∈ ℚ := sorry
  have : √2 > 0 := sorry
  -- have : ∃ {a, b: ℕ // a ≠ 0, b ≠ 0}, b*√2 = a
  let f:= (cofinite : Filter ℕ ) Ultrafilter.of (ℕ :=
  Classical.choose (exists_le f)
  f:= Ultrafilter.of
  let S:={p : ℕ | p.Prime ∧ (p : ZMod 8) = 3}
  have : Infinite S:=setOf_prime_and_eq_mod_infinite (h3 : IsUnit 3)
  have : Denumerable S:= sorry

  have ∀p∈ S: ¬ IsSquare (2: ZMod p):= exists_sq_eq_two_iff
  map (g: ℕ → S) (f : Ultrafilter ℕ) : Ultrafilter S :=
  ofComplNotMemIff (map g f) fun s => @compl_not_mem_iff _ f (g ⁻¹' s)


-- #eval IsSquare

/-- **Łoś's Theorem**: A sentence is true in an ultraproduct if and only if the set of structures
it is true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)
  show False
  exact h3 h4


/-
theorem disc_fnct : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  apply byContradiction
  intro (h1: ¬ (∃ f : ℝ → ℝ, ¬ Continuous f))
  have h2 : ∀ f : ℝ → ℝ, Continuous f := by
    not_exists_not (f : ℝ → ℝ, Continuous f)
  let S := Set ℝ → ℝ
  let T := Set ℝ
  have h3 : ¬ (#S ≤ #T) := by
    have : #T = 𝔠 := mk_univ_real
    have : #S = 𝔠^𝔠 := power_def 𝔠 𝔠
    have : #S = 2^𝔠 := power_self_eq 𝔠
    have : #T < #S := cantor 𝔠
    apply lt_iff_le_not_le
  def F (f : ℝ → ℝ) (q : ℚ) : ℝ :=
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
-/
