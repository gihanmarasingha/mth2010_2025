import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

def f : Polynomial ℚ := 3 * X + 1

def g : Polynomial ℚ := 5 * X^2 + 3

example : f + g = 5 * X ^ 2 + 3 * X + 4 := by
  simp [f, g]
  ring

example : f * g = (15 * X ^ 3 + 5 * X ^ 2 + 9 * X + 3) := by
  simp [f, g]
  ring

example : f.eval 2 = 7 := by
  simp [f]
  norm_num

end section

#min_imports
