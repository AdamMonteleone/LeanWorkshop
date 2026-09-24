import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Week2Solutions

/-! # Workshop Sheet - Week 3: Groups -/

namespace WorkshopWeek3

variable {G H : Type*} [Group G] [Group H]

/-! ## 1. Rapid-fire group facts

`[Group G]` supplies multiplication, the identity `1`, and inverses.
The group need not be commutative: the order of factors matters.

Useful lemmas: `mul_assoc`, `mul_one`, `one_mul`, `inv_mul_cancel`,
`mul_inv_cancel`, `mul_inv_rev`, and `pow_add`.
Try `simp` for the first two parts and `rw` for the others.
-/

-- 1(a): a * 1 = a.
lemma mul_one_warmup (a : G) : a * 1 = a := by
  sorry

-- 1(b): a⁻¹ * a = 1.
lemma inv_mul_warmup (a : G) : a⁻¹ * a = 1 := by
  sorry

-- 1(c): a⁻¹ * (a * b) = b.
lemma inv_mul_mul_warmup (a b : G) : a⁻¹ * (a * b) = b := by
  sorry

-- 1(d): (a * b)⁻¹ = b⁻¹ * a⁻¹.
lemma mul_inv_warmup (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

-- 1(e): (a * b) * b⁻¹ = a.
lemma mul_mul_inv_warmup (a b : G) : (a * b) * b⁻¹ = a := by
  sorry

-- 1(f): a² * a³ = a⁵.
lemma powers_warmup (a : G) : a ^ 2 * a ^ 3 = a ^ 5 := by
  sorry

/-! ## 2. Subgroups

Let S be a nonempty subset of G, closed under a * b⁻¹.
Parts (a)-(c) establish the three subgroup properties; part (d) assembles them
to prove the subgroup test.

`S.Nonempty` means ∃ a, a ∈ S.
`hclosed a ha b hb` proves a * b⁻¹ ∈ S from ha : a ∈ S and hb : b ∈ S.
Reuse the earlier parts to construct the subgroup in 2(d).
-/

-- 2(a): A nonempty set closed under a * b⁻¹ contains 1.
lemma one_mem_of_test (S : Set G) (hne : S.Nonempty)
    (hclosed : ∀ a ∈ S, ∀ b ∈ S, a * b⁻¹ ∈ S) : (1 : G) ∈ S := by
  sorry

-- 2(b): It is closed under inverses. Apply hclosed to 1 and a, using 2(a).
lemma inv_mem_of_test (S : Set G) (hne : S.Nonempty)
    (hclosed : ∀ a ∈ S, ∀ b ∈ S, a * b⁻¹ ∈ S)
    (a : G) (ha : a ∈ S) : a⁻¹ ∈ S := by
  sorry

-- 2(c): It is closed under multiplication. Apply hclosed to a and b⁻¹, using 2(b).
lemma mul_mem_of_test (S : Set G) (hne : S.Nonempty)
    (hclosed : ∀ a ∈ S, ∀ b ∈ S, a * b⁻¹ ∈ S)
    (a b : G) (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S := by
  sorry

-- 2(d): Prove the following theorem (Subgroup test).
-- A nonempty subset S of a group G, closed under a * b⁻¹, is a subgroup of G.
-- Constructing a Subgroup G with carrier S formalizes this conclusion.
-- Reuse (a)-(c) to construct the subgroup yourself.
def subgroupOfTest (S : Set G) (hne : S.Nonempty)
    (hclosed : ∀ a ∈ S, ∀ b ∈ S, a * b⁻¹ ∈ S) : Subgroup G := by
  sorry

/-! ## 3. Homomorphisms, kernels and images

`f : G →* H` is a group homomorphism.
Use `map_one f`, `map_mul f a b`, and `map_inv f a` for its basic properties.

In 3(b) and 3(c), apply your subgroup test from Question 2(d).
The supplied first line leaves two goals: nonemptiness and closure under x * y⁻¹.
For the image, reuse last week's witnesses for membership in f '' S.
-/

-- 3(a): A homomorphism preserves a * b⁻¹.
lemma map_mul_inv (f : G →* H) (a b : G) : f (a * b⁻¹) = f a * (f b)⁻¹ := by
  sorry

-- 3(b): Use Question 2(d) to construct the kernel subgroup.
def kernelSubgroup (f : G →* H) : Subgroup G := by
  apply subgroupOfTest {a : G | f a = 1}
  · sorry
  · sorry

-- 3(c): Use Question 2(d) to construct the image subgroup.
def imageSubgroup (f : G →* H) : Subgroup H := by
  apply subgroupOfTest (f '' (Set.univ : Set G))
  · sorry
  · sorry

-- From here on, use Mathlib's kernel f.ker and image f.range.

-- 3(d): The key calculation for equality of cosets modulo the kernel.
-- Hint: use change to expose kernel membership; inv_mul_eq_one handles the last step.
lemma inv_mul_mem_ker_iff (f : G →* H) (a b : G) :
    a⁻¹ * b ∈ f.ker ↔ f a = f b := by
  sorry

/-! ## 4. The first isomorphism theorem

We will prove G / ker(f) ≃ im(f), without assuming that f is surjective onto H.

Mathlib supplies the normality of f.ker and the quotient group `G ⧸ f.ker`.
Write `QuotientGroup.mk' f.ker a` for the coset [a].
The next two supplied facts let us choose representatives and test coset equality.
This is the general-group version of the class-equality question from Week 2.
-/

-- Supplied: every coset has a representative.
lemma exists_representative (f : G →* H) (q : G ⧸ f.ker) :
    ∃ a : G, QuotientGroup.mk' f.ker a = q :=
  QuotientGroup.mk'_surjective f.ker q

-- Supplied: the equality criterion for cosets.
lemma coset_eq_iff (f : G →* H) (a b : G) :
    QuotientGroup.mk' f.ker a = QuotientGroup.mk' f.ker b ↔ a⁻¹ * b ∈ f.ker :=
  QuotientGroup.eq

-- 4(a): [a] = [b] ↔ f(a) = f(b). Use the supplied criterion and 3(d).
lemma class_eq_iff (f : G →* H) (a b : G) :
    QuotientGroup.mk' f.ker a = QuotientGroup.mk' f.ker b ↔ f a = f b := by
  sorry

/-!
The induced homomorphism sends [a] to f(a), viewed as an element of the image.
Part 4(a) explains why its value does not depend on the representative.

An element `y : f.range` consists of:
* `y.val : H`, its underlying value;
* `y.property : ∃ a, f a = y.val`, a proof that it lies in the image.

`f.rangeRestrict : G →* f.range` is f with its codomain restricted to its image.
`Subtype.ext` proves equality of two image elements from equality of their values.
Conversely, `congrArg Subtype.val h` takes an equality h in the image to one in H.
-/

-- Supplied construction: QuotientGroup.lift descends a homomorphism to a quotient.
-- Its last argument checks that elements of the subgroup map to the identity.
def toImage (f : G →* H) : G ⧸ f.ker →* f.range :=
  QuotientGroup.lift f.ker f.rangeRestrict (by
    intro a ha
    change f.rangeRestrict a = 1
    apply Subtype.ext
    exact ha)

-- Supplied evaluation rule: the induced map sends [a] to f(a).
lemma toImage_mk (f : G →* H) (a : G) :
    toImage f (QuotientGroup.mk' f.ker a) = f.rangeRestrict a := rfl

-- 4(b): The induced homomorphism is injective.
-- Hint: after intro q r h, use obtain ⟨a, rfl⟩ := exists_representative f q,
-- and similarly for r. Use 4(a) and congrArg Subtype.val h.
lemma toImage_injective (f : G →* H) : Function.Injective (toImage f) := by
  sorry

-- 4(c): The induced homomorphism is surjective onto the image.
-- Hint: for y : f.range, obtain a preimage from y.property and use its coset.
-- Use Subtype.ext to reduce the remaining equality to an equality in H.
lemma toImage_surjective (f : G →* H) : Function.Surjective (toImage f) := by
  sorry

-- 4(d): Assemble the isomorphism using 4(b) and 4(c).
-- A multiplicative equivalence (≃*) is a group isomorphism.
-- MulEquiv.ofBijective packages a bijective homomorphism as an isomorphism.
-- It is noncomputable because its inverse is chosen from the surjectivity proof.
noncomputable def firstIsomorphism (f : G →* H) : G ⧸ f.ker ≃* f.range :=
  MulEquiv.ofBijective (toImage f) (by
    constructor
    · sorry
    · sorry)

open WorkshopWeek2Solutions

/-! ## 5. An application: the Chinese remainder theorem

We will use the first isomorphism theorem to prove
`ZMod 6 ≃+ ZMod 2 × ZMod 3`, then generalise to any positive coprime moduli.
These are isomorphisms of additive groups.
Here `ZMod n` means the integers modulo n. An additive homomorphism is written
`A →+ B`, and an additive group isomorphism is written `A ≃+ B`.

Recall Week 2's `Congruent n a b := n ∣ (b - a)`.
`(a : ZMod n)` is the residue class of an integer a modulo n.
We supply the residue maps and the additive version of Question 4 below.
-/

-- Supplied: the quotient map from integers to residues.
def residue (n : ℕ) : ℤ →+ ZMod n := Int.castAddHom (ZMod n)

-- Supplied: reduce simultaneously modulo 2 and modulo 3.
def residuePair : ℤ →+ ZMod 2 × ZMod 3 :=
  (residue 2).prod (residue 3)

-- 5(a): The residue-class relation is precisely last week's relation.
-- Mathlib's ZMod.intCast_eq_intCast_iff_dvd_sub a b n states this for integer casts.
lemma residue_eq_iff (n : ℕ) (a b : ℤ) :
    residue n a = residue n b ↔ Congruent (n : ℤ) a b := by
  sorry

-- Supplied integer arithmetic: divisibility by 6 means divisibility by 2 and 3.
lemma six_dvd_iff (z : ℤ) : (6 : ℤ) ∣ z ↔ (2 : ℤ) ∣ z ∧ (3 : ℤ) ∣ z := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    constructor
    · use 3 * k
      rw [hk]
      ring
    · use 2 * k
      rw [hk]
      ring
  · intro h
    obtain ⟨a, ha⟩ := h.left
    obtain ⟨b, hb⟩ := h.right
    use a - b
    calc
      z = 3 * z - 2 * z := by ring
      _ = 3 * (2 * a) - 2 * (3 * b) := by rw [← ha, ← hb]
      _ = 6 * (a - b) := by ring

-- Supplied: apply 5(a) with a = 0 to read kernel membership as divisibility.
lemma mem_residue_ker (n : ℕ) (z : ℤ) :
    z ∈ (residue n).ker ↔ (n : ℤ) ∣ z := by
  change residue n z = 0 ↔ (n : ℤ) ∣ z
  rw [← map_zero (residue n), eq_comm, residue_eq_iff]
  change (n : ℤ) ∣ (z - 0) ↔ (n : ℤ) ∣ z
  rw [sub_zero]

-- 5(b): Both kernels are the multiples of 6.
-- Hint: after the supplied lines, use mem_residue_ker and six_dvd_iff.
lemma residuePair_ker : residuePair.ker = (residue 6).ker := by
  ext z
  change (residue 2 z, residue 3 z) = (0, 0) ↔ z ∈ (residue 6).ker
  rw [Prod.mk.injEq, mem_residue_ker]
  change (z ∈ (residue 2).ker ∧ z ∈ (residue 3).ker) ↔ (6 : ℤ) ∣ z
  sorry

-- Supplied arithmetic on residues, proved by computing these four small values.
lemma three_mod_two : (3 : ZMod 2) = 1 := by decide
lemma four_mod_two : (4 : ZMod 2) = 0 := by decide
lemma three_mod_three : (3 : ZMod 3) = 0 := by decide
lemma four_mod_three : (4 : ZMod 3) = 1 := by decide

-- 5(c): Choose integer representatives a,b. The integer 3*a+4*b maps to (x,y).
-- The supplied lines choose the representatives and separate the two coordinates.
-- Use the cast rules Int.cast_add, Int.cast_mul, Int.cast_ofNat;
-- the four arithmetic facts above; and ha or hb.
lemma residuePair_surjective : Function.Surjective residuePair := by
  intro xy
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective xy.1
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective xy.2
  use 3 * a + 4 * b
  apply Prod.ext
  · change ((3 * a + 4 * b : ℤ) : ZMod 2) = xy.1
    sorry
  · change ((3 * a + 4 * b : ℤ) : ZMod 3) = xy.2
    sorry

-- Supplied: the additive, surjective version of Question 4.
noncomputable def additiveFirstIsomorphism {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) : A ⧸ f.ker ≃+ B :=
  QuotientAddGroup.quotientKerEquivOfSurjective f hf

-- Supplied: the ordinary residue quotient is ZMod n, by the same theorem.
noncomputable def residueQuotient (n : ℕ) : ℤ ⧸ (residue n).ker ≃+ ZMod n :=
  additiveFirstIsomorphism (residue n) ZMod.intCast_surjective

-- 5(d): Use the first isomorphism theorem and the kernel calculation.
-- Fill the first hole using additiveFirstIsomorphism and 5(c).
-- Then rewrite its source using 5(b) and compose with (residueQuotient 6).symm.
-- e.symm reverses an isomorphism; e.trans d composes e followed by d.
noncomputable def chineseRemainderSix : ZMod 6 ≃+ ZMod 2 × ZMod 3 := by
  have e : ℤ ⧸ residuePair.ker ≃+ ZMod 2 × ZMod 3 := by
    sorry
  sorry

/-! ### 5(e). The Chinese remainder theorem

Prove and formalize the following theorem by generalising (b)-(d).
For positive coprime integers m,n, the additive groups
`ZMod m × ZMod n` and `ZMod (m * n)` are isomorphic.

Here `hcop : m.Coprime n` is the hypothesis gcd(m,n) = 1.
We supply two integer-arithmetic facts. Prove the general kernel calculation
and surjectivity, then use the first isomorphism theorem as in 5(d).
-/

-- 5(e): Prove the Chinese remainder theorem using the steps below.
-- Supplied: reduce simultaneously modulo m and modulo n.
def generalResiduePair (m n : ℕ) : ℤ →+ ZMod m × ZMod n :=
  (residue m).prod (residue n)

-- Supplied Bézout identity: obtain ⟨u, v, huv⟩ := bezout_coefficients m n hcop.
lemma bezout_coefficients (m n : ℕ) (hcop : m.Coprime n) :
    ∃ u v : ℤ, (m : ℤ) * u + (n : ℤ) * v = 1 := by
  use Nat.gcdA m n, Nat.gcdB m n
  rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
  rfl

-- Supplied: the general version of six_dvd_iff.
lemma coprime_mul_dvd_iff (m n : ℕ) (hcop : m.Coprime n) (z : ℤ) :
    ((m * n : ℕ) : ℤ) ∣ z ↔ (m : ℤ) ∣ z ∧ (n : ℤ) ∣ z := by
  rw [Nat.cast_mul]
  constructor
  · intro h
    constructor
    · exact dvd_trans (dvd_mul_right (m : ℤ) (n : ℤ)) h
    · exact dvd_trans (dvd_mul_left (n : ℤ) (m : ℤ)) h
  · intro h
    obtain ⟨a, ha⟩ := h.left
    obtain ⟨b, hb⟩ := h.right
    obtain ⟨u, v, huv⟩ := bezout_coefficients m n hcop
    use u * b + v * a
    calc
      z = ((m : ℤ) * u + (n : ℤ) * v) * z := by rw [huv, one_mul]
      _ = (m : ℤ) * u * ((n : ℤ) * b) + (n : ℤ) * v * ((m : ℤ) * a) := by
        rw [add_mul, ← ha, ← hb]
      _ = (m : ℤ) * (n : ℤ) * (u * b + v * a) := by ring

-- Generalise 5(b), using coprime_mul_dvd_iff instead of six_dvd_iff.
lemma generalResiduePair_ker (m n : ℕ) (hcop : m.Coprime n) :
    (generalResiduePair m n).ker = (residue (m * n)).ker := by
  sorry

-- Generalise 5(c). If m*u + n*v = 1 and a,b represent x,y, use n*v*a + m*u*b.
-- Casting the Bezout identity modulo m and modulo n gives the two coefficients
-- that equal 1. Use congrArg and the cast rules from 5(c), together with
-- Int.cast_natCast, Int.cast_one and ZMod.natCast_self.
lemma generalResiduePair_surjective (m n : ℕ) (hcop : m.Coprime n) :
    Function.Surjective (generalResiduePair m n) := by
  sorry

-- Assemble the isomorphism as in 5(d), then use .symm for the stated direction.
noncomputable def chineseRemainderCoprime (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n)
    (hcop : m.Coprime n) : ZMod m × ZMod n ≃+ ZMod (m * n) := by
  sorry

end WorkshopWeek3
