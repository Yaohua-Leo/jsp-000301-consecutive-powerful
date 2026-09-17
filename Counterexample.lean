/-
JSP-000301: formalization of the consecutive powerful-number counterexample
12167 and 12168.

Scope: this file formalizes the six theorems fixed in the problem statement,
namely the negation of "if two consecutive positive integers are powerful then
at least one of them is a perfect square".

12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2 are counterexamples already present in
the literature (Golomb 1970, also treated by Walker 1976). This file is a
formalization of that known counterexample. It claims no new mathematical
discovery and does not address the counting question of Erdos problem #365.

The imports are the exact set validated by the environment check, rather than
the Mathlib umbrella module.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith

namespace JSP301

/-- A powerful number: a positive integer whose every prime factor divides it
with exponent at least two. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- If `a * a < n` and `n < (a + 1) * (a + 1)`, then `n` is not a square.
The conclusion holds for an arbitrary candidate square root, not only for
finitely many checked roots. -/
lemma not_square_of_sq_lt_and_lt_sq {n a : ℕ} (hlo : a * a < n)
    (hhi : n < (a + 1) * (a + 1)) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have h1 : a < r := by
    by_contra h
    have hle : r ≤ a := not_lt.mp h
    refine absurd (Nat.mul_le_mul hle hle) ?_
    rw [← hr]
    exact not_le.mpr hlo
  have h2 : r < a + 1 := by
    by_contra h
    have hle : a + 1 ≤ r := not_lt.mp h
    refine absurd (Nat.mul_le_mul hle hle) ?_
    rw [← hr]
    exact not_le.mpr hhi
  exact absurd h2 (not_lt_of_ge (Nat.succ_le_of_lt h1))

/-- If `p` and `q` are both prime and `p ∣ q ^ k`, then `p = q`. -/
lemma eq_of_prime_dvd_prime_pow {p q k : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : p ∣ q ^ k) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)

/-- 12167 = 23^3 is a powerful number. -/
theorem powerful_12167 : Powerful 12167 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hpd
  have hcube : (23 : ℕ) ^ 3 = 12167 := by norm_num
  have hp23 : p ∣ 23 := hp.dvd_of_dvd_pow (hcube ▸ hpd)
  have hpeq : p = 23 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp23
  subst hpeq
  exact ⟨23, by norm_num⟩

/-- 12168 = 2^3 * 3^2 * 13^2 is a powerful number. -/
theorem powerful_12168 : Powerful 12168 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hpd
  have hfac : (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by norm_num
  have hdiv : p ∣ (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 := hfac ▸ hpd
  rcases hp.dvd_mul.mp hdiv with h | h
  · rcases hp.dvd_mul.mp h with h2 | h3
    · have hpeq : p = 2 := eq_of_prime_dvd_prime_pow hp (by norm_num) h2
      subst hpeq
      exact ⟨3042, by norm_num⟩
    · have hpeq : p = 3 := eq_of_prime_dvd_prime_pow hp (by norm_num) h3
      subst hpeq
      exact ⟨1352, by norm_num⟩
  · have hpeq : p = 13 := eq_of_prime_dvd_prime_pow hp (by norm_num) h
    subst hpeq
    exact ⟨72, by norm_num⟩

/-- 12167 is not a square: 110^2 < 12167 < 111^2. -/
theorem not_square_12167 : ¬ IsSquare (12167 : ℕ) :=
  not_square_of_sq_lt_and_lt_sq (by norm_num : 110 * 110 < 12167)
    (by norm_num : 12167 < 111 * 111)

/-- 12168 is not a square: 110^2 < 12168 < 111^2. -/
theorem not_square_12168 : ¬ IsSquare (12168 : ℕ) :=
  not_square_of_sq_lt_and_lt_sq (by norm_num : 110 * 110 < 12168)
    (by norm_num : 12168 < 111 * 111)

/-- There exist two consecutive positive powerful numbers, neither of which is a
square. -/
theorem jsp301_counterexample :
  ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
    ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, by norm_num, powerful_12167, by simpa using powerful_12168,
   not_square_12167, by simpa using not_square_12168⟩

/-- The negation of the original question: not every pair of consecutive
positive powerful numbers contains a square. -/
theorem jsp301_false :
  ¬ (∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
    IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 (by norm_num) powerful_12167 (by simpa using powerful_12168) with hsq | hsq
  · exact not_square_12167 hsq
  · exact not_square_12168 (by simpa using hsq)

end JSP301
