import Mathlib

open Pointwise

variable {R} [CommRing R] [DecidableEq R]

variable (I J : Ideal R)

/-
## Using ideal properties

Here are the three main properties that define an ideal and how to use them.
-/

example : 0 ∈ I := by apply zero_mem

example {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by apply add_mem hx hy

example {x r : R} (hx : x ∈ I) : r * x ∈ I := by apply Ideal.mul_mem_left _ _ hx

/-
## Sum of ideals
-/

@[simp]
def sum_carrier : Set R :=  {x | ∃ a ∈ I, ∃ b ∈ J, x = a + b}

def sum : Ideal R where
  carrier := sum_carrier I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ sum_carrier I J → x₂ ∈ sum_carrier I J → x₁ + x₂ ∈ sum_carrier I J
    rintro x₁ x₂ ⟨a₁, ha₁, b₁, hb₁, hx₁⟩ ⟨a₂, ha₂, b₂, hb₂, hx₂⟩
    simp
    use a₁ + a₂, ?_, b₁ + b₂, ?_
    · rw [hx₁, hx₂]
      ring
    · apply add_mem ha₁ ha₂
    apply add_mem hb₁ hb₂ -- sorry
  zero_mem' := by
    show 0 ∈ sum_carrier I J
    simp
    use 0, ?_, 0, ?_ -- sorry copy the `use` above
    all_goals simp
  smul_mem' := by
    show ∀ r x, x ∈ sum_carrier I J → r * x ∈ sum_carrier I J
    rintro r x ⟨a, ha, b, hb, hx⟩
    simp
    rw [hx]
    use r * a, ?_, r * b, ?_
    · ring
    · apply Ideal.mul_mem_left _ _ ha
    apply Ideal.mul_mem_left _ _ hb

@[simp]
def prod_carrier := {x | ∃ s : Finset (R × R),
        (∀ p ∈ s, p.1 ∈ I ∧ p.2 ∈ J) ∧
        x = ∑ p ∈ s, p.1 * p.2 }

def prod : Ideal R where
  carrier := prod_carrier I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ prod_carrier I J → x₂ ∈ prod_carrier I J → x₁ + x₂ ∈ prod_carrier I J
    rintro x₁ x₂ hx₁' hx₂'
    rcases hx₁' with ⟨s₁, hm₁, hx₁⟩
    rcases hx₂' with ⟨s₂, hm₂, hx₂⟩
    simp
    use s₁ ∪ s₂
    sorry

  zero_mem' := sorry
  smul_mem' := sorry
