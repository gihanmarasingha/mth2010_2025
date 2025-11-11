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
    _ = (-a) * b + (a * b + -(a * b)) := by rw [add_neg_cancel]
    _ = ((-a) * b + a * b) + -(a * b) := by rw [add_assoc]
    _ = 0 + -(a * b) := by rw [h]
    _ = -(a * b) + 0 := by rw [add_comm]
    _ = -(a * b) := by rw [add_zero]
  calc (-a) * b + (a * b) = b * (-a) + b * a := by rw [mul_comm _ b, mul_comm _ b]
    _ = b * (-a + a) := by rw [left_distrib]
    _ = b * (a + -a) := by rw [add_comm]
    _ = b * 0 := by rw [add_neg_cancel]
    _ = 0 := by rw [←mul_zero]

lemma neg_neg : -(-a) = a := by
  calc
    -(-a) = -(-a) + 0 := by rw [add_zero]
    _ = -(-a) + (a + -a) := by rw [add_neg_cancel]
    _ = -(-a) + (-a + a) := by rw [add_comm a]
    _ = (-(-a) + -a) + a := by rw [add_assoc]
    _ = (-a + -(-a)) + a := by rw [add_comm (-a)]
    _ = 0 + a := by rw [add_neg_cancel]
    _ = a + 0 := by rw [add_comm]
    _ = a := by rw [add_zero]

lemma neg_mul_neg : (-a) * (-b) = a * b := by
  calc
    (-a) * (-b) = -(a * (-b)) := by rw [neg_mul]
    _ = -((-b) * a) := by rw [mul_comm]
    _ = -(-(b * a)) := by rw [neg_mul]
    _ = -(-(a * b)) := by rw [mul_comm]
    _ = a * b := by rw [neg_neg]

lemma neg_eq_neg_one_mul : -a = (-1) * a := by
  sorry



end examples
