import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Workshop Sheet - Week 1: Lean skeleton

Exercise labels match the sheet: 1(a)–(h), 2(a)–(f), and 3(a)–(e).
Replace each `sorry` as you go. The last part of Exercises 2 and 3 is a
partially filled main proof; its earlier parts prepare the steps you need.

Place your cursor inside a proof to see the current goal and available
hypotheses in Lean's Infoview. A `sorry` is an unfinished proof placeholder;
its warning is expected until you replace it. Start with `intro`, `exact`,
`refine`, `rfl`, `rw`, `simp`, `rcases`, and `norm_num`. The warm-up also
introduces `linarith` and `nlinarith` for inequalities; further tactics are explained where needed.

You are not expected to know mathlib lemma names. Search for a relevant
fact in Loogle (https://loogle.lean-lang.org/), then hover over a name
or use `#check` on a separate line outside a proof to inspect its type.
Match the required hypotheses to the facts available in your proof.
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
example (n : ℕ) (h : n = 2 ∨ n = 3) : n ^ 2 ≤ 9 := by
    sorry

-- 1(f): Bound a real variable using two inequalities.
example (x y : ℝ) (h₁ : x + y ≤ 7) (h₂ : 3 ≤ y) : x ≤ 4 := by
    sorry

-- 1(g): A square plus one is positive.
example (x : ℝ) : 0 < x ^ 2 + 1 := by
    sorry

-- 1(h): Calculate with rational numbers.
example : (3 : ℚ) / 4 + 1 / 6 = 11 / 12 := by
    sorry

/-! ## Exercise 2: infinitely many primes -/

-- 2(a): Bound a prime divisor.
example (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hdiv : p ∣ n) :
    2 ≤ p ∧ p ≤ n := by
    sorry

-- 2(b): A prime cannot divide consecutive natural numbers.
example (p m : ℕ) (hp : Nat.Prime p) (hprev : p ∣ m)
    (hnext : p ∣ m + 1) : False := by
    sorry

-- 2(c): Two is the only even prime.
example (p : ℕ) (hp : Nat.Prime p) (heven : 2 ∣ p) : p = 2 := by
    sorry

-- 2(d): Find a prime divisor of n! + 1.
-- First prove `have hN : n.factorial + 1 ≠ 1 := by ...`
-- using `have hpos := Nat.factorial_pos n` and `linarith`.
-- Nat.exists_prime_and_dvd takes hN and supplies the required prime divisor.
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
    obtain ⟨p, hp, hdiv⟩ := prime_divisor_factorial_add_one n
    refine ⟨p, hp, ?_⟩
    sorry

/-! ## Exercise 3: the square root of two is irrational
The first four parts prepare a parity argument for a fraction in lowest terms.
-/

-- Each named lemma below is available for use in later proofs.

-- 3(a): Prove divisibility with a witness.
lemma two_dvd_double (k : ℤ) : (2 : ℤ) ∣ 2 * k := by
    sorry

-- 3(b): An even square has an even root.
-- Hint: inspect `Int.prime_two.dvd_mul`
lemma even_of_even_square (n : ℤ) (hsq : (2 : ℤ) ∣ n * n) :
    (2 : ℤ) ∣ n := by
    sorry

-- 3(c): Substitute into a squared equation.
-- Hint: rewrite hn in hsq with `rw [hn] at hsq`, then use `nlinarith`.
lemma denominator_square_after_substitution (n d k : ℤ) (hsq : n ^ 2 = d ^ 2 * 2)
    (hn : n = 2 * k) : d * d = 2 * k * k := by
    sorry

-- 3(d): Coprime numbers cannot both be even.
lemma coprime_not_both_even (n d : ℕ) (hc : Nat.Coprime n d) (hn : 2 ∣ n) (hd : 2 ∣ d) :
    False := by
    sorry

/-! ### 3(e): formalize the statement and proof that √2 is irrational-/
theorem sqrt_two_by_parity : Irrational (Real.sqrt 2) := by
    sorry


end WorkshopWeek1
