import Mathlib

/-
# Properties of Rings
-/

variable {R : Type*} [CommRing R]

/-
## Ring axioms
-/

variable (a b c : R)

example : a + b = b + a := by apply add_comm

example : a + 0 = a := by apply add_zero

example : a + (-a) = 0 := by apply add_neg_cancel

example : (a + b) + c = a + (b + c) := by apply add_assoc

example : a * b = b * a := by apply mul_comm

example : (a * b) * c = a * (b * c) := by apply mul_assoc

example : a * (b + c) = a * b + a * c := by apply left_distrib

example : a * 1 = a := by apply mul_one


/-
# Example

Complete the following proof, adding lines of calculation as necessary.
The proof in each line should be of the form `rw [axiom]`, where `axiom` is
one of the axioms given above *or* one of the lemmas you've already proved while
doing this sheet.

-/

namespace examples

lemma mul_zero (a : R) : 0 = a * 0 := by
  calc
    0 = (a * 0) + -(a * 0) := by rw [add_neg_cancel]
    _ = (a * (0 + 0)) + -(a * 0) := by rw [add_zero]
    _ = ((a * 0) + (a * 0)) + -(a * 0) := by rw [left_distrib]
    _ = (a * 0) + ((a * 0) + -(a * 0)) := by rw [add_assoc]
    _ = a * 0 + 0 := by rw [add_neg_cancel]
    _ = a * 0 := by rw [add_zero]

lemma neg_mul : (-a) * b = -(a * b) := by
  suffices h : (-a) * b + (a * b) = 0 by
    calc (-a) * b = (-a) * b + 0 := by rw [add_zero]
    _ = -(a * b) := by sorry
  calc (-a) * b + (a * b) = sorry := by sorry
    _ = 0 := by sorry


lemma neg_mul_neg : (-a) * (-b) = a * b := by
  sorry

lemma mul_one : (-a) * 1 = -a := by
  sorry



end examples
