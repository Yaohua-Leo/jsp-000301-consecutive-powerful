import Counterexample

-- Restatement checks. Each `example` below re-states a claim in expanded form,
-- without reference to the definitions used inside the proof, so that a reader
-- can compare it against the original question.

example (n : ℕ) : JSP301.Powerful n ↔
    (0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n) := Iff.rfl

example : 0 < (12167 : ℕ) ∧
    ∀ p : ℕ, Nat.Prime p → p ∣ 12167 → p ^ 2 ∣ 12167 :=
  JSP301.powerful_12167
example : 0 < (12168 : ℕ) ∧
    ∀ p : ℕ, Nat.Prime p → p ∣ 12168 → p ^ 2 ∣ 12168 :=
  JSP301.powerful_12168
example : ¬ (∃ r : ℕ, 12167 = r * r) := JSP301.not_square_12167
example : ¬ (∃ r : ℕ, 12168 = r * r) := JSP301.not_square_12168
example : ∃ n : ℕ, 0 < n ∧ JSP301.Powerful n ∧ JSP301.Powerful (n + 1) ∧
    ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := JSP301.jsp301_counterexample

-- The negated original question, stated without the local `Powerful` predicate.
example : ¬ (∀ n : ℕ, 0 < n →
    (0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n) →
    (0 < n + 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n + 1 → p ^ 2 ∣ n + 1) →
    (∃ r : ℕ, n = r * r) ∨ (∃ r : ℕ, n + 1 = r * r)) := JSP301.jsp301_false

-- Axiom audit. Each line prints the axioms the named theorem depends on.
#print axioms JSP301.powerful_12167
#print axioms JSP301.powerful_12168
#print axioms JSP301.not_square_12167
#print axioms JSP301.not_square_12168
#print axioms JSP301.jsp301_counterexample
#print axioms JSP301.jsp301_false
