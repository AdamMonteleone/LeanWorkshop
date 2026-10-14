import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Nat.Choose.Sum

/-!
# Lean Workshop 4: Rings and Modules
-/

namespace WorkshopWeek4

variable {A : Type*} [CommRing A]

-- 1(a): Prove the inverse criterion directly from the definition of IsUnit.
-- `IsUnit x` means `∃ u : Aˣ, (u : A) = x`;
lemma unit_iff_exists_inverse (x : A) :
    IsUnit x ↔ ∃ y : A, x * y = 1 := by
  sorry

-- 1(b): If x² = 0, use (a) to prove that 1 + x is a unit.
-- `add_mul` and `mul_sub` express distributivity; `pow_two` gives x² = x * x.
lemma one_add_unit_of_square_zero (x : A) (hx : x ^ 2 = 0) :
    IsUnit (1 + x) := by
  sorry

-- 1(c): Prove that an inverse is unique.
-- `mul_assoc` changes brackets; `mul_comm` exchanges two factors.
lemma inverse_unique (x y z : A) (hxy : x * y = 1) (hxz : x * z = 1) :
    y = z := by
  sorry

-- 1(d): Prove that the product of two units is a unit using part (a).
lemma product_of_units_is_unit (x y : A) (hx : IsUnit x) (hy : IsUnit y) :
    IsUnit (x * y) := by
  sorry

/-! ## 1(e)-(f). Sums of nilpotent elements

`add_pow` is Mathlib's binomial theorem.
`pow_eq_zero_of_le h hx` gives x^k = 0 from h : m ≤ k and hx : x^m = 0.
`Finset.sum_eq_zero` says a finite sum is zero when every summand is zero.
-/

-- Supplied arithmetic fact.
lemma binomial_index_cases (m n i : ℕ) : m ≤ i ∨ n ≤ m + n - i := by
  omega

-- 1(e): Prove (x + y)^(m + n) = 0 when x^m = 0 and y^n = 0.
theorem nilpotent_add_pow_eq_zero (x y : A) {m n : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) : (x + y) ^ (m + n) = 0 := by
  -- Supplied binomial expansion.
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro i _hi
  sorry

-- 1(f): Deduce that a sum of nilpotent elements is nilpotent.
theorem nilpotent_add (x y : A) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x + y) := by
  sorry

variable {B : Type*} [CommRing B]

/-! ## 2. Prime ideals and the nilradical

To construct an `Ideal A`, supply `carrier` and these closure proofs:
* `zero_mem'`: 0 belongs to the ideal;
* `add_mem'`: x and y belonging implies x + y belongs;
* `smul_mem'`: x belonging implies a • x belongs for every a : A.
Here `a • x = a * x`. For `I : Ideal A`, `hx : x ∈ I`, `hy : y ∈ I`, use:
* `I.zero_mem : (0 : A) ∈ I`;
* `I.add_mem hx hy : x + y ∈ I`;
* `I.mul_mem_left a hx : a * x ∈ I`.

To prove `P.IsPrime`, supply:
* `ne_top' : P ≠ ⊤` (where `⊤` is the whole ring);
* `mem_or_mem' : ∀ {a b}, a * b ∈ P → a ∈ P ∨ b ∈ P`.
For `hP : P.IsPrime`, use `hP.ne_top`, `hP.mem_or_mem hab` and
`hP.one_notMem`, where `hab : a * b ∈ P`; the last says 1 ∉ P.

`Ideal.mem_bot` states x ∈ (⊥ : Ideal A) ↔ x = 0.
`Ideal.eq_top_iff_one I` states I = ⊤ ↔ 1 ∈ I.
-/

-- 2(a): Construct the preimage ideal f⁻¹(J).
-- `map_zero`, `map_one`, `map_add` and `map_mul` express preservation of 0, 1, + and *.
-- `J.mul_mem_left b ha` gives b * a ∈ J from ha : a ∈ J.
def idealPreimage (f : A →+* B) (J : Ideal B) : Ideal A where
  carrier := {r : A | f r ∈ J}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

-- 2(b): The preimage of a prime ideal is prime.
theorem idealPreimage_prime (f : A →+* B) (P : Ideal B) (hP : P.IsPrime) :
    (idealPreimage f P).IsPrime := by
  sorry

-- 2(c): Construct the ideal of nilpotent elements.
-- `mul_pow` states (a * b)^n = a^n * b^n in a commutative ring.
def nilradicalIdeal (A : Type*) [CommRing A] : Ideal A where
  carrier := {x | IsNilpotent x}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

-- Supplied identification with Mathlib's nilradical.
-- `mem_nilradical` states x ∈ nilradical A ↔ IsNilpotent x.
lemma nilradicalIdeal_eq_mathlib (A : Type*) [CommRing A] :
    nilradicalIdeal A = nilradical A := by
  ext x
  change IsNilpotent x ↔ x ∈ nilradical A
  exact mem_nilradical.symm

-- 2(d) (Challenge): The nilradical is the intersection of all prime ideals.
-- `sInf S` is an intersection; `Submodule.mem_sInf` states
-- x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I.
-- For hP : P.IsPrime, `hP.mem_of_pow_mem n` gives x ∈ P from x^n ∈ P.
-- `Ideal.exists_le_prime_disjoint I S h` is Mathlib's Zorn-lemma result:
-- if I is disjoint from a submonoid S, there is a prime P containing I
-- and disjoint from S. Its result is ∃ P, P.IsPrime ∧ I ≤ P ∧ Disjoint (P : Set A) S.
-- `Submonoid.powers x` consists of powers of x. `Submonoid.mem_powers_iff`
-- states y ∈ Submonoid.powers x ↔ ∃ n : ℕ, x^n = y.
-- `Submonoid.mem_powers x` asserts x ∈ Submonoid.powers x.
-- `Set.disjoint_left` states that disjoint sets have no common element.
lemma nilradicalIdeal_eq_intersection_primes (A : Type*) [CommRing A] :
    nilradicalIdeal A = sInf {P : Ideal A | P.IsPrime} := by
  sorry

variable {M : Type*} [AddCommGroup M] [Module A M]

/-! ## 3. Modules and annihilators

`Submodule A M` is the type of A-submodules of M. Mathlib's scalar identities:
* `zero_smul`: (0 : A) • m = 0;
* `add_smul`: (a + b) • m = a • m + b • m;
* `mul_smul`: (a * b) • m = a • (b • m);
* `smul_zero`: a • (0 : M) = 0;
* `one_smul`: (1 : A) • m = m.
-/

-- 3(a): Construct the cyclic submodule Am.
def cyclicSubmodule (m : M) : Submodule A M := by
  exact {
    carrier := {x : M | ∃ r : A, r • m = x}
    zero_mem' := by
      sorry
    add_mem' := by
      sorry
    smul_mem' := by
      sorry
  }

-- 3(b): Construct Ann(m) = {a : A | a • m = 0} as an ideal.
def annihilator (m : M) : Ideal A := by
  exact {
    carrier := {r : A | r • m = 0}
    zero_mem' := by
      sorry
    add_mem' := by
      sorry
    smul_mem' := by
      sorry
  }

-- 3(c): The annihilator of a nonzero element is proper.
theorem annihilator_ne_top (m : M) (hm : m ≠ 0) :
    annihilator (A := A) m ≠ ⊤ := by
  sorry

-- 3(d): A nonzero vector over a field has zero annihilator.
-- `[Field A] [Module A M]` makes M a vector space over A.
-- `inv_mul_cancel₀ ha` gives a⁻¹ * a = 1 when ha : a ≠ 0.
theorem annihilator_eq_bot_of_field {A M : Type*}
    [Field A] [AddCommGroup M] [Module A M] (m : M) (hm : m ≠ 0) :
    annihilator (A := A) m = ⊥ := by
  sorry

-- Supplied: Ann(M) is the ideal of scalars annihilating every element of M.
def moduleAnnihilator : Ideal A where
  carrier := {r : A | ∀ m : M, r • m = 0}
  zero_mem' := by
    intro m
    exact zero_smul A m
  add_mem' := by
    intro a b ha hb m
    change (a + b) • m = 0
    rw [add_smul, ha m, hb m, add_zero]
  smul_mem' := by
    intro c a ha m
    change (c * a) • m = 0
    rw [mul_smul, ha m, smul_zero]

-- `⨅ m : M, annihilator m` is the intersection of the ideals Ann(m).
-- `Submodule.mem_iInf` characterizes membership in an indexed intersection.
-- Supplied specialization to this family.
lemma mem_intersection_annihilators (r : A) :
    r ∈ (⨅ m : M, annihilator (A := A) m) ↔
      ∀ m : M, r ∈ annihilator (A := A) m := by
  exact Submodule.mem_iInf (fun m : M => annihilator (A := A) m)

-- 3(e): Ann(M) is the intersection of Ann(m) over all m ∈ M.
theorem moduleAnnihilator_eq_intersection :
    moduleAnnihilator (A := A) (M := M) =
      ⨅ m : M, annihilator (A := A) m := by
  sorry

/-! ## 4. Compute with vectors and matrices -/
def D : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 0, 1]
def v : Fin 2 → ℚ := ![3, 4]

-- Supplied: a computable inverse using Matrix.det and Matrix.adjugate.
local instance : Inv (Matrix (Fin 2) (Fin 2) ℚ) where
  inv T := T.det⁻¹ • T.adjugate

-- 4(a): Matrix-vector product.


-- 4(b): Determinant.

-- 4(c): Inverse.


end WorkshopWeek4
