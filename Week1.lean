import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Workshop Sheet - Week 1: Lean skeleton

Exercise labels match the sheet: 1(a)–(i), 2(a)–(f), and 3(a)–(f).
Replace each `sorry` as you go. The last part of Exercises 2 and 3 is the
main proof; its earlier parts prepare the steps you need.

Place your cursor inside a proof to see the current goal and available
hypotheses in Lean's Infoview. A `sorry` is an unfinished proof placeholder;
its warning is expected until you replace it. Start with `intro`, `exact`,
`apply`, `use`, `rfl`, `rw`, `simp`, `rcases`, and `norm_num`. The warm-up also
introduces `linarith`, `positivity`, and `nlinarith`.

You are not expected to know mathlib lemma names. Search for a relevant
fact in Loogle (https://loogle.lean-lang.org/), then hover over a name
or use `#check` on a separate line outside a proof to inspect its type.
Match the required hypotheses to the facts available in your proof.
If stuck, consult the solutions for a suitable lemma name.
-/

namespace WorkshopWeek1

/-! ## Exercise 1: Tactic practice -/

-- 1(a): Use an assumption.
example (P : Prop) : P → P := by
    sorry

-- 1(b): Supply a witness.
example (k : ℕ) : ∃ m : ℕ, m = k := by
    sorry

-- 1(c): relabelling preserves equality.
example (a b : ℤ) (h : a = b) : a + 1 = b + 1 := by
    sorry

-- 1(d): Subtract from a successor.
example (m : ℕ) : m + 1 - m = 1 := by
    sorry

-- 1(e): Bound a square.
-- For alternatives, `rcases h with h1 | h2` creates one branch per case.
example (n : ℕ) (h : n = 2 ∨ n = 3) : n ^ 2 ≤ 9 := by
    sorry

-- 1(f): Bound a real variable using two inequalities.
example (x y : ℝ) (h₁ : x + y ≤ 7) (h₂ : 3 ≤ y) : x ≤ 4 := by
    sorry

-- 1(g): A square plus one is positive.
example (x : ℝ) : 0 < x ^ 2 + 1 := by
    sorry

-- 1(h): Bound a number from its square.
example (x : ℝ) (h : x ^ 2 ≤ 4) : x ≤ 2 := by
    sorry

-- 1(i): Calculate with rational numbers.
example : (3 : ℚ) / 4 + 1 / 6 = 11 / 12 := by
    sorry

/-! ## Exercise 2: infinitely many primes
Parts (d) and (e) provide the two lemmas for the prime proof in (f).
-/

-- 2(a): Find a larger natural number.
example (n : ℕ) : ∃ m : ℕ, n < m := by
    sorry

-- 2(b): Add multiples.
-- For an existential, `rcases h with ⟨u, hu⟩` names a witness and its property.
example (d a b : ℕ) (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
    sorry

-- 2(c): Divisibility is transitive.
example (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
    sorry

/-! Worked example: composing proofs (not an exercise).
`have` records an intermediate fact. `apply` changes a conclusion into its premise.
-/
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
    have hQ : Q := by
        apply hPQ  -- To prove Q using P → Q, the new goal is P.
        exact hP
    apply hQR      -- To prove R using Q → R, the new goal is Q.
    exact hQ

-- 2(d): Find a prime divisor of n! + 1.
lemma prime_divisor_factorial_add_one (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n.factorial + 1 := by
    sorry

-- 2(e): A small prime cannot divide n! + 1.
lemma prime_divisor_factorial_add_one_contradiction (n p : ℕ)
    (hp : Nat.Prime p) (hle : p ≤ n) (hdiv : p ∣ n.factorial + 1) :
    False := by
    sorry

/-! ### 2(f): infinitely many primes
Use the above lemmas to formalize the statement and proof of the following theorem.
Theorem: there are infinitely many primes.
-/

theorem primes_above_every_bound (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p := by
    -- ∧ means "and": this existential supplies p together with two proofs.
    -- `obtain` unpacks a newly obtained proof, like `rcases` on a hypothesis.
    obtain ⟨p, hp, hdiv⟩ := prime_divisor_factorial_add_one n
    use p, hp
    sorry

/-! ## Exercise 3: the square root of two is irrational
Parts (a)–(e) are lemmas for the parity argument.
-/

-- Each named lemma below is available for use in later proofs.

-- 3(a): Divisibility from a squared equation.
lemma two_dvd_square_of_eq_two_mul_square (a b : ℤ) (hsq : a ^ 2 = 2 * b ^ 2) :
    (2 : ℤ) ∣ a ^ 2 := by
    sorry

-- 3(b): An even square has an even root.
lemma even_of_even_square (a : ℤ) (hsq : (2 : ℤ) ∣ a ^ 2) :
    (2 : ℤ) ∣ a := by
    sorry

-- 3(c): A squared equation forces evenness.
lemma even_of_square_eq_two_mul_square (a b : ℤ) (hsq : a ^ 2 = 2 * b ^ 2) :
    (2 : ℤ) ∣ a := by
    sorry

-- 3(d): Substitute into a squared equation.
lemma denominator_square_after_substitution (a b k : ℤ) (hsq : a ^ 2 = 2 * b ^ 2)
    (ha : a = 2 * k) : b ^ 2 = 2 * k ^ 2 := by
    sorry

-- 3(e): Coprime numbers cannot both be even.
-- A common divisor divides the greatest common divisor.
lemma coprime_not_both_even (a b : ℕ) (hc : Nat.Coprime a b) (ha : 2 ∣ a) (hb : 2 ∣ b) :
    False := by
    sorry

/-! ### 3(f): formalize the statement and proof that √2 is irrational
The rational representation and type-conversion code below is supplied.
-/

theorem sqrt_two_by_parity : Irrational (Real.sqrt 2) := by
    rw [irrational_iff_ne_rational]
    intro r s hs h
    have hsq_real : ((r : ℝ) / (s : ℝ)) * ((r : ℝ) / (s : ℝ)) = 2 := by
        rw [← h]
        norm_num
    -- Both sides are rational values, so the real equality gives a rational equality.
    have hsq_rat : ((r : ℚ) / (s : ℚ)) * ((r : ℚ) / (s : ℚ)) = 2 := by
        exact_mod_cast hsq_real  -- Read the same equality between rational values in ℚ.
    let q : ℚ := (r : ℚ) / (s : ℚ)
    have hq : q * q = 2 := by
        exact hsq_rat
    rw [← Rat.num_div_den q] at hq  -- Express q using its reduced numerator and denominator.
    field_simp at hq  -- Clear the denominators in this squared equation.
    let a : ℤ := q.num
    let b : ℕ := q.den
    have hsq_int : a ^ 2 = 2 * (b : ℤ) ^ 2 := by
        rw [mul_comm (2 : ℤ) ((b : ℤ) ^ 2)]
        exact_mod_cast hq  -- Express a² = 2b² in ℤ rather than ℚ.
    have hcoprime : Nat.Coprime a.natAbs b := q.reduced  -- gcd(|a|, b) = 1.
    -- These are two small conversion helpers, not new assumptions about the fraction.
    -- Each m is a temporary input used only inside its own helper; hm proves it is even.
    -- toNatAbs: if an integer m is even, its absolute value (a natural number) is even.
    have toNatAbs (m : ℤ) (hm : (2 : ℤ) ∣ m) : (2 : ℕ) ∣ m.natAbs := by
        rw [← Int.natCast_dvd]  -- Rewrite 2 ∣ |m| in ℕ as 2 ∣ m in ℤ.
        exact hm  -- This is precisely the hypothesis hm.
    -- toNat: if a natural number m is even when viewed as an integer, it is even in ℕ.
    have toNat (m : ℕ) (hm : (2 : ℤ) ∣ (m : ℤ)) : (2 : ℕ) ∣ m := by
        exact_mod_cast hm  -- Remove the cast: conclude 2 ∣ m in ℕ.
    sorry


end WorkshopWeek1
