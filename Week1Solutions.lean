import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Workshop Sheet - Week 1: complete Lean solutions

Worked solutions to the seventeen preparatory exercises and two main proofs.
Exercise labels match the sheet: 1(a)–(h), 2(a)–(f), and 3(a)–(e).
-/

namespace WorkshopWeek1Solutions

/-! ## Exercise 1: Tactic practice -/

-- 1(a): Use an assumption.
example (P : Prop) : P → P := by
    intro hP
    exact hP

-- 1(b): Supply a witness.
example (k : ℕ) : ∃ m : ℕ, m = k := by
    refine ⟨k, ?_⟩
    rfl

-- 1(c): relabelling preserves equality.
example (a b : ℤ) (h : a = b) : a + 1 = b + 1 := by
    rw [h]

-- 1(d): Subtract from a successor.
example (m : ℕ) : m + 1 - m = 1 := by
    simp

-- 1(e): Bound a square.
example (n : ℕ) (h : n = 2 ∨ n = 3) : n ^ 2 ≤ 9 := by
    rcases h with htwo | hthree
    · rw [htwo]
      norm_num
    · rw [hthree]
      norm_num

-- 1(f): Bound a real variable using two inequalities.
example (x y : ℝ) (h₁ : x + y ≤ 7) (h₂ : 3 ≤ y) : x ≤ 4 := by
    linarith

-- 1(g): A square plus one is positive.
example (x : ℝ) : 0 < x ^ 2 + 1 := by
    nlinarith

-- 1(h): Calculate with rational numbers.
example : (3 : ℚ) / 4 + 1 / 6 = 11 / 12 := by
    norm_num

/-! ## Exercise 2: infinitely many primes -/

-- 2(a): Bound a prime divisor.
example (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hdiv : p ∣ n) :
    2 ≤ p ∧ p ≤ n := by
    exact ⟨hp.two_le, Nat.le_of_dvd hn hdiv⟩

-- 2(b): A prime cannot divide consecutive natural numbers.
example (p m : ℕ) (hp : Nat.Prime p) (hprev : p ∣ m)
    (hnext : p ∣ m + 1) : False := by
    have hone : p ∣ 1 := by
        simpa using Nat.dvd_sub hnext hprev
    exact hp.not_dvd_one hone

-- 2(c): Two is the only even prime.
example (p : ℕ) (hp : Nat.Prime p) (heven : 2 ∣ p) : p = 2 := by
    rw [Nat.dvd_prime hp] at heven
    rcases heven with h | h
    · norm_num at h
    · linarith

-- 2(d): Find a prime divisor of n! + 1.
-- First prove `have hN : n.factorial + 1 ≠ 1 := by ...`
-- using `have hpos := Nat.factorial_pos n` and `linarith`.
-- Nat.exists_prime_and_dvd takes hN and supplies the required prime divisor.
-- Nat.exists_prime_and_dvd needs N ≠ 1. For N > 1, existence follows
-- by taking its least divisor greater than one: if composite, a smaller
-- nontrivial factor would divide N. Full prime factorization is not needed.
lemma prime_divisor_factorial_add_one (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n.factorial + 1 := by
    have hN : n.factorial + 1 ≠ 1 := by
        have hpos := Nat.factorial_pos n
        linarith
    exact Nat.exists_prime_and_dvd hN

-- 2(e): A small prime cannot divide n! + 1.
-- Nat.dvd_factorial needs positivity (hp.pos) and the bound hle.
-- Nat.dvd_sub then gives divisibility of (n! + 1) - n!, hence of 1.
lemma prime_divisor_factorial_add_one_contradiction (n p : ℕ)
    (hp : Nat.Prime p) (hle : p ≤ n) (hdiv : p ∣ n.factorial + 1) :
    False := by
    have hfac : p ∣ n.factorial := Nat.dvd_factorial hp.pos hle
    have hone : p ∣ 1 := by
        simpa using Nat.dvd_sub hdiv hfac
    exact hp.not_dvd_one hone

/-! ### 2(f): infinitely many primes
Use the above lemmas to formalize the statement and proof of the following theorem.
Theorem: there are infinitely many primes.

For any n, choose a prime divisor p of n! + 1. If p were at most n,
it would also divide n!, hence 1, contradicting primality. Thus p > n.
Every finite set of natural numbers is bounded, so there are infinitely
many primes.
-/

theorem primes_above_every_bound (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p := by
    obtain ⟨p, hp, hdiv⟩ := prime_divisor_factorial_add_one n
    refine ⟨p, hp, ?_⟩
    by_contra h
    have hle : p ≤ n := by linarith
    exact prime_divisor_factorial_add_one_contradiction n p hp hle hdiv

/-! ## Exercise 3: the square root of two is irrational
The first four parts prepare a parity argument for a fraction in lowest terms.
-/

-- Each named lemma below is available for use in later proofs.

-- 3(a): Prove divisibility with a witness.
lemma two_dvd_double (k : ℤ) : (2 : ℤ) ∣ 2 * k := by
    refine ⟨k, ?_⟩
    rfl

-- 3(b): An even square has an even root.
-- Hint: inspect `Int.prime_two.dvd_mul`
lemma even_of_even_square (n : ℤ) (hsq : (2 : ℤ) ∣ n * n) :
    (2 : ℤ) ∣ n := by
    rw [Int.prime_two.dvd_mul] at hsq
    rcases hsq with h | h
    · exact h
    · exact h

-- 3(c): Substitute into a squared equation.
-- Hint: rewrite hn in hsq with `rw [hn] at hsq`, then use `nlinarith`.
lemma denominator_square_after_substitution (n d k : ℤ) (hsq : n ^ 2 = d ^ 2 * 2)
    (hn : n = 2 * k) : d * d = 2 * k * k := by
    rw [hn] at hsq
    nlinarith

-- 3(d): Coprime numbers cannot both be even.
-- A common divisor of coprime numbers is itself coprime to itself.
lemma coprime_not_both_even (n d : ℕ) (hc : Nat.Coprime n d) (hn : 2 ∣ n) (hd : 2 ∣ d) :
    False := by
    have hcoprime2 : Nat.Coprime 2 2 := Nat.Coprime.of_dvd hn hd hc
    norm_num at hcoprime2


/-! ### 3(e): formalize the statement and proof that √2 is irrational -/

theorem sqrt_two_by_parity : Irrational (Real.sqrt 2) := by
    rw [irrational_iff_ne_rational]
    intro a b hb h
    have hsq_real : ((a : ℝ) / (b : ℝ)) * ((a : ℝ) / (b : ℝ)) = 2 := by
        rw [← h]
        norm_num
    have hsq_rat : ((a : ℚ) / (b : ℚ)) * ((a : ℚ) / (b : ℚ)) = 2 := by
        exact_mod_cast hsq_real
    let q : ℚ := (a : ℚ) / (b : ℚ)
    have hq : q * q = 2 := by
        exact hsq_rat
    rw [← Rat.num_div_den q] at hq
    field_simp at hq
    -- With n = q.num and d = q.den, next restate n^2 = 2*d^2 in the integers.
    have hsq_int : q.num ^ 2 = (q.den : ℤ) ^ 2 * 2 := by
        exact_mod_cast hq
    -- Exercise 3(a): the squared equation shows the numerator's square is even.
    have htwo_dvd_num_sq : (2 : ℤ) ∣ q.num * q.num := by
        rw [← pow_two, hsq_int, mul_comm]
        exact two_dvd_double ((q.den : ℤ) ^ 2)
    -- Exercise 3(b): an even square has an even root.
    have htwo_dvd_num : (2 : ℤ) ∣ q.num := by
        exact even_of_even_square q.num htwo_dvd_num_sq
    obtain ⟨k, hk⟩ := htwo_dvd_num
    -- Exercise 3(c): substitute the even numerator into the squared equation.
    have hden_sq : (q.den : ℤ) * (q.den : ℤ) = 2 * k * k := by
        exact denominator_square_after_substitution q.num (q.den : ℤ) k hsq_int hk
    -- Exercises 3(a) and 3(b): the denominator is also even.
    have htwo_dvd_den_sq : (2 : ℤ) ∣ (q.den : ℤ) * (q.den : ℤ) := by
        rw [hden_sq, mul_assoc]
        exact two_dvd_double (k * k)
    have htwo_dvd_den_int : (2 : ℤ) ∣ (q.den : ℤ) := by
        exact even_of_even_square (q.den : ℤ) htwo_dvd_den_sq
    -- Express divisibility in the natural numbers used by q.reduced.
    have htwo_dvd_num_abs : 2 ∣ q.num.natAbs := by
        rw [← Int.natCast_dvd]
        exact ⟨k, hk⟩
    have htwo_dvd_den : 2 ∣ q.den := by
        exact_mod_cast htwo_dvd_den_int
    -- Exercise 3(d): a reduced fraction cannot have both numerator and denominator even.
    exact coprime_not_both_even q.num.natAbs q.den q.reduced htwo_dvd_num_abs htwo_dvd_den


end WorkshopWeek1Solutions
