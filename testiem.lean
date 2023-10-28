import Mathlib.Tactic.Linarith

def aux0 (A B: Nat): A <= 1 -> B <= 1 -> A + B <= 2 := by
  intros H1 H2
  linarith
