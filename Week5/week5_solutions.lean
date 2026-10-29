import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Workshop Sheet - Week 5: Topology -/

namespace WorkshopWeek5

open Filter Topology

variable {α β γ ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/- ## Filters, convergence -/

-- These are the defining properties of a filter:

example (s s' : Set α) (L : Filter α) (h : s ⊆ s') (hL : s ∈ L) : s' ∈ L := by
  sorry

example (L : Filter α) : Set.univ ∈ L := by
  sorry

example (s s' : Set α) (L : Filter α) (hL : s ∈ L) (hL' : s' ∈ L) : s ∩ s' ∈ L := by
  sorry

-- A filter `L` is finer than `L'` if for every set `s ∈ L'` we have `s ∈ L`:

example (L L' : Filter α) : L ≤ L' ↔ ∀ s ∈ L', s ∈ L := by
  sorry

-- `⊥` is the trivial filter containing only `Set.univ`
example (L : Filter α) : ⊥ ≤ L := by
  sorry

-- `⊤` is the trivial filter containing all sets
example (L : Filter α) : L ≤ ⊤ := by
  sorry

-- We can transport filters along maps:
example (f : α → β) (L : Filter α) (L' : Filter β) :
    L.map f = L' ↔ ∀ (s : Set β), s ∈ Filter.map f L ↔ s ∈ L' := by
  sorry

-- Convergence is called `Filter.Tendsto` and is defined as
example (f : α → β) (L : Filter α) (L' : Filter β) : L.Tendsto f L' ↔ L.map f ≤ L' := by
  sorry

-- composition of limits
example (f : α → β) (g : β → γ) (L : Filter α) (L' : Filter β) (L'' : Filter γ)
    (hf : L.Tendsto f L') (hg : L'.Tendsto g L'') : L.Tendsto (g ∘ f) L'' := by
  sorry

/- ## Typical convergence questions on ℝ -/

example (L : Filter ℝ) (c : ℝ) : L.Tendsto (fun _ : ℝ ↦ c) (𝓝 c) := by
  exact tendsto_const_nhds

example (f : ℝ → ℝ) (g : ℝ → ℝ) (L : Filter ℝ) (hf : L.Tendsto f (𝓝 0)) (hg : L.Tendsto g (𝓝 1)) :
    L.Tendsto (f + g) (𝓝 1) := by
  rw [Pi.add_def f g]
  simpa using hf.add hg

example : Filter.atTop.Tendsto (fun x : ℝ ↦ 1 / x) (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  use max 1 (1 + 1 / ε)
  intro δ hδ
  simp
  have hδ' : 1 ≤ δ := by grind
  have hδ'' : 1 + 1 / ε ≤ δ := by grind
  field_simp
  rw [abs_of_pos (by positivity)]
  grw [← hδ'']
  grind

/- ## Eventually and frequently -/

example (L : Filter α) (p : α → Prop) : (∀ᶠ x in L, p x) ↔ {x | p x} ∈ L := by
  sorry

example (L : Filter α) (p : α → Prop) : (∃ᶠ x in L, p x) ↔ ∀ U, U ∈ L → ∃ x ∈ U, p x := by
  sorry

example (L : Filter α) (p p' : α → Prop) (hp : ∀ᶠ x in L, p x) (hp' : ∀ᶠ x in L, p' x) :
    ∀ᶠ x in L, p x ∧ p' x := by
  filter_upwards [hp, hp'] with x hp hp'
  exact ⟨hp, hp'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

example (f : ℝ → ℝ) (L : Filter ℝ) : L.Tendsto f atTop ↔ ∀ b, ∀ᶠ x in L, b ≤ f x := by
  sorry

example (f : ℝ → ℝ) (g : ℝ → ℝ) (L : Filter ℝ)
    (hf : L.Tendsto f Filter.atTop) (h : ∀ x, f x ≤ g x) : L.Tendsto g Filter.atTop := by
  rw [tendsto_atTop] at hf ⊢
  intro b
  filter_upwards [hf b] with x hf
  grw [hf, h]

/- # Continuity -/


example {f : ℝ → ℝ} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  sorry

example (x : ℝ) (hx : x ≠ 0) (r : ℝ) : ContinuousAt (fun y ↦ y ^ r) x := by
  sorry


end WorkshopWeek5
