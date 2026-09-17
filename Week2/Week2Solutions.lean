import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ring

/-! # Workshop Sheet Solutions - Week 2: Sets, Functions and Relations -/

namespace WorkshopWeek2Solutions

variable {X Y Z : Type*}

/-! ## 1. Set theory -/

-- 1(a): x ∈ S and x ∈ T imply x ∈ S ∩ T.
lemma mem_inter_of_mem (S T : Set X) (x : X) (hS : x ∈ S) (hT : x ∈ T) : x ∈ S ∩ T := by
  constructor
  · exact hS
  · exact hT

-- 1(b): x ∈ S ∩ T → x ∈ S.
lemma mem_of_mem_inter (S T : Set X) (x : X) (h : x ∈ S ∩ T) : x ∈ S := by
  exact h.left

-- 1(c): S ⊆ T and x ∈ S imply x ∈ T.
lemma mem_of_subset (S T : Set X) (x : X) (h : S ⊆ T) (hx : x ∈ S) : x ∈ T := by
  exact h hx

-- 1(d): f(x) ∈ U → x ∈ f⁻¹(U).
lemma mem_preimage_of_mem (f : X → Y) (U : Set Y) (x : X) (h : f x ∈ U) : x ∈ f ⁻¹' U := by
  exact h

-- 1(e): x ∈ S → f(x) ∈ f(S).
lemma mem_image_of_mem (f : X → Y) (S : Set X) (x : X) (hx : x ∈ S) : f x ∈ f '' S := by
  use x

-- 1(f): f(S ∩ T) ⊆ f(S) ∩ f(T).
lemma image_inter_subset (f : X → Y) (S T : Set X) :
    f '' (S ∩ T) ⊆ f '' S ∩ f '' T := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  constructor
  · rw[← hx.right]
    apply Set.mem_image_of_mem f
    exact hx.left.left
  · rw[← hx.right]
    apply Set.mem_image_of_mem f
    exact hx.left.right

-- 1(g): f(S ∩ f⁻¹(U)) = f(S) ∩ U.
lemma image_inter_preimage (f : X → Y) (S : Set X) (U : Set Y) :
    f '' (S ∩ f ⁻¹' U) = f '' S ∩ U := by
  ext y
  constructor
  · intro h
    obtain ⟨hS, hImPre⟩ := Set.image_inter_subset f S (f ⁻¹' U) h
    constructor
    · exact hS
    · apply Set.image_preimage_subset f U
      exact hImPre
  · intro h
    obtain ⟨x , hx⟩ := h.left
    apply Set.mem_of_eq_of_mem hx.right.symm
    apply mem_image_of_mem f (S ∩ f ⁻¹' U) x
    constructor
    · exact hx.left
    · apply mem_preimage_of_mem f U x
      apply Set.mem_of_eq_of_mem hx.right
      exact h.right

-- 1(h): 𝒫(S ∩ T) = 𝒫(S) ∩ 𝒫(T).
lemma powerset_inter (S T : Set X) : 𝒫 (S ∩ T) = 𝒫 S ∩ 𝒫 T := by
  ext A
  constructor
  · intro hA   -- A ⊆ S ∩ T.
    constructor
    · intro a ha
      -- Use 1(c): a ∈ A and A ⊆ S ∩ T give a ∈ S ∩ T.
      obtain ⟨haS, haT⟩ := mem_of_subset A (S ∩ T) a hA ha
      exact haS
    · intro a ha
      obtain ⟨haS, haT⟩ := mem_of_subset A (S ∩ T) a hA ha
      exact haT
  · intro hA
    obtain ⟨hAS, hAT⟩ := hA
    intro a ha
    -- Use 1(a): prove a ∈ S and a ∈ T.
    apply mem_inter_of_mem S T a
    · apply mem_of_subset A S a hAS -- Use 1(c) with A ⊆ S.
      exact ha
    · apply mem_of_subset A T a hAT  -- Use 1(c) with A ⊆ T.
      exact ha

/-! ## 2. Functions -/

-- 2(a): If g ∘ f is injective, then f is injective.
lemma injective_of_comp (f : X → Y) (g : Y → Z)
    (hcomp : Function.Injective (g ∘ f)) : Function.Injective f := by
  intro x y h
  apply hcomp
  change g (f x) = g (f y) -- changes g ∘ f x = g ∘ f y to g(f(x)) = g(f(y))
  rw [h]

-- 2(b): If g ∘ f is surjective, then g is surjective.
lemma surjective_of_comp (f : X → Y) (g : Y → Z)
    (hcomp : Function.Surjective (g ∘ f)) : Function.Surjective g := by
  intro z
  obtain ⟨x, hx⟩ := hcomp z
  use f x
  exact hx

-- 2(c): If r ∘ f = id and f ∘ s = id, then r = s. Hint: congrFun
lemma inverse_unique (f : X → Y) (r s : Y → X)
    (hr : r ∘ f = id) (hs : f ∘ s = id) : r = s := by
  ext y
  have h₁ : r (f (s y)) = s y := congrFun hr (s y)
  have h₂ : f (s y) = y := congrFun hs y
  rw [h₂] at h₁ -- r(y) = r(f(s(y))) = id(s(y)) = s(y)
  exact h₁

-- 2(d): The singleton map X → 𝒫(X), x ↦ {x}, is injective.
lemma singleton_injective : Function.Injective (fun x : X => ({x} : Set X)) := by
  intro x y h
  change ({x} : Set X) = ({y} : Set X) at h
  change x ∈ ({y} : Set X)
  simp [← h]

-- 2(e): Prove and formalize Cantor’s theorem.
-- Theorem: For every set X, there is no surjection X → 𝒫(X).
-- Hint: consider the diagonal set D = {x | x ∉ f x}.
lemma cantor_not_surjective (f : X → Set X) : ¬ Function.Surjective f := by
  intro hf
  let D : Set X := {x | x ∉ f x}
  obtain ⟨a, ha⟩ := hf D
  have hnot : a ∉ D := by
    intro haD
    have hna : a ∉ f a := haD
    have hfa : a ∈ f a := by
      rw [ha]
      exact haD
    exact hna hfa
  have haD : a ∈ D := by
    change a ∉ f a
    rw [ha]
    exact hnot
  exact hnot haD

/-! ## 3. Relations

Fix n ∈ ℤ. Write a ∼ b when n ∣ (b - a).
-/

def Congruent (n a b : ℤ) : Prop := n ∣ (b - a)

-- 3(a): a ∼ a.
lemma congruent_refl (n a : ℤ) : Congruent n a a := by
  change ∃ k : ℤ, a - a = n * k
  use 0
  simp

-- 3(b): a ∼ b → b ∼ a.
lemma congruent_symm (n a b : ℤ) (hab : Congruent n a b) : Congruent n b a := by
  obtain ⟨k, hk⟩ := hab
  change ∃ l : ℤ, a - b = n * l
  use -k
  calc
    a - b = -(b - a) := by ring
    _ = -(n * k) := by rw [hk]
    _ = n * (-k) := by ring

-- 3(c): a ∼ b and b ∼ c imply a ∼ c.
lemma congruent_trans (n a b c : ℤ)
    (hab : Congruent n a b) (hbc : Congruent n b c) : Congruent n a c := by
  rcases hab with ⟨k, hk⟩
  rcases hbc with ⟨l, hl⟩
  change ∃ m : ℤ, c - a = n * m
  use k + l
  calc
    c - a = (b - a) + (c - b) := by ring
    _ = n * k + n * l := by rw [hk, hl]
    _ = n * (k + l) := by ring

-- 3(d): Congruence modulo n is an equivalence relation.
lemma congruent_equivalence (n : ℤ) : Equivalence (Congruent n) := by
  constructor
  · intro a
    exact congruent_refl n a
  · intro a b hab
    exact congruent_symm n a b hab
  · intro a b c hab hbc
    exact congruent_trans n a b c hab hbc

-- 3(e): a ∼ a′ and b ∼ b′ imply a + b ∼ a′ + b′.
lemma congruent_add (n a a' b b' : ℤ)
    (haa' : Congruent n a a') (hbb' : Congruent n b b') :
    Congruent n (a + b) (a' + b') := by
  rcases haa' with ⟨k, hk⟩
  rcases hbb' with ⟨l, hl⟩
  change ∃ m : ℤ, (a' + b') - (a + b) = n * m
  use k + l
  calc
    (a' + b') - (a + b) = (a' - a) + (b' - b) := by ring
    _ = n * k + n * l := by rw [hk, hl]
    _ = n * (k + l) := by ring

def congruenceClass (n a : ℤ) : Set ℤ := {b | Congruent n a b}

-- 3(f): [a] = [b] ↔ a ∼ b, where [a] = {b | a ∼ b}.
lemma congruenceClass_eq_iff (n a b : ℤ) :
    congruenceClass n a = congruenceClass n b ↔ Congruent n a b := by
  constructor
  · intro h
    have hb : b ∈ congruenceClass n b := congruent_refl n b
    rw [← h] at hb
    exact hb
  · intro hab
    ext x
    constructor
    · intro hax
      exact congruent_trans n b a x (congruent_symm n a b hab) hax
    · intro hbx
      exact congruent_trans n a b x hab hbx

end WorkshopWeek2Solutions
