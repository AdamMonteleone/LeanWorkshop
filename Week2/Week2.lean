import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ring

/-! # Workshop Sheet - Week 2: Sets, Functions and Relations -/

namespace WorkshopWeek2

variable {X Y Z : Type*}

/-! ## 1. Set theory -/

-- 1(a): x ∈ S and x ∈ T imply x ∈ S ∩ T.
lemma mem_inter_of_mem (S T : Set X) (x : X) (hS : x ∈ S) (hT : x ∈ T) : x ∈ S ∩ T := by
  sorry

-- 1(b): x ∈ S ∩ T → x ∈ S.
lemma mem_of_mem_inter (S T : Set X) (x : X) (h : x ∈ S ∩ T) : x ∈ S := by
  sorry

-- 1(c): S ⊆ T and x ∈ S imply x ∈ T.
lemma mem_of_subset (S T : Set X) (x : X) (h : S ⊆ T) (hₓ : x ∈ S) : x ∈ T := by
  sorry

-- 1(d): f(x) ∈ U → x ∈ f⁻¹(U).
lemma mem_preimage_of_mem (f : X → Y) (U : Set Y) (x : X) (h : f x ∈ U) : x ∈ f ⁻¹' U := by
  sorry

-- 1(e): x ∈ S → f(x) ∈ f(S).
lemma mem_image_of_mem (f : X → Y) (S : Set X) (x : X) (hₓ : x ∈ S) : f x ∈ f '' S := by
  sorry

-- 1(f): f(S ∩ T) ⊆ f(S) ∩ f(T).
lemma image_inter_subset (f : X → Y) (S T : Set X) :
    f '' (S ∩ T) ⊆ f '' S ∩ f '' T := by
  sorry


/-! ## 2. Functions -/

-- 2(a): If g ∘ f is injective, then f is injective.
lemma injective_of_comp (f : X → Y) (g : Y → Z)
    (hcomp : Function.Injective (g ∘ f)) : Function.Injective f := by
  sorry


-- 2(b): If g ∘ f is surjective, then g is surjective.
lemma surjective_of_comp (f : X → Y) (g : Y → Z)
    (hcomp : Function.Surjective (g ∘ f)) : Function.Surjective g := by
  sorry

-- 2(c): If r ∘ f = id and f ∘ s = id, then r = s.
lemma inverse_unique (f : X → Y) (r s : Y → X)
    (hᵣ : r ∘ f = id) (hₛ : f ∘ s = id) : r = s := by
  sorry



-- 2(d): The singleton map X → 𝒫(X), x ↦ {x}, is injective.
lemma singleton_injective : Function.Injective (fun x : X => ({x} : Set X)) := by
  sorry

-- 2(e): Prove and formalize Cantor’s theorem.
-- Theorem: For every set X, there is no surjection X → 𝒫(X).
-- Hint: consider the diagonal set D = {x | x ∉ f x}.
lemma cantor_not_surjective (f : X → Set X) : ¬ Function.Surjective f := by
  sorry

/-! ## 3. Relations

Fix n ∈ ℤ. Write a ∼ b when n ∣ (b - a).
-/

def Congruent (n a b : ℤ) : Prop := n ∣ (b - a)

-- 3(a): a ∼ a.
lemma congruent_refl (n a : ℤ) : Congruent n a a := by
  sorry

-- 3(b): a ∼ b → b ∼ a.
lemma congruent_symm (n a b : ℤ) (h₁ : Congruent n a b) : Congruent n b a := by
  sorry

-- 3(c): a ∼ b and b ∼ c imply a ∼ c.
lemma congruent_trans (n a b c : ℤ)
    (h₁ : Congruent n a b) (h₂ : Congruent n b c) : Congruent n a c := by
  sorry

-- 3(d): Congruence modulo n is an equivalence relation.
lemma congruent_equivalence (n : ℤ) : Equivalence (Congruent n) := by
  sorry

-- 3(e): a ∼ a′ and b ∼ b′ imply a + b ∼ a′ + b′.
lemma congruent_add (n a a' b b' : ℤ)
    (h₁ : Congruent n a a') (h₂ : Congruent n b b') :
    Congruent n (a + b) (a' + b') := by
  sorry

def congruenceClass (n a : ℤ) : Set ℤ := {b | Congruent n a b}

-- 3(f): [a] = [b] ↔ a ∼ b, where [a] = {b | a ∼ b}.
lemma congruenceClass_eq_iff (n a b : ℤ) :
    congruenceClass n a = congruenceClass n b ↔ Congruent n a b := by
  sorry

end WorkshopWeek2
