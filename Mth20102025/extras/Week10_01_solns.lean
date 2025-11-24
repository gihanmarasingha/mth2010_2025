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
def prod_carrier : Set R :=
  {x | ∃ (ι : Type*) (_ : Fintype ι)
        (a b : ι → R),
        (∀ i, a i ∈ I ∧ b i ∈ J) ∧
        x = ∑ i, a i * b i }

/- def prod : Ideal R where
  carrier := prod_carrier I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ prod_carrier I J → x₂ ∈ prod_carrier I J → x₁ + x₂ ∈ prod_carrier I J
    rintro x₁ x₂ hx₁' hx₂'
    simp at hx₁'
    rcases hx₁' with ⟨ι₁, hι₁, a₁, b₁, h₁, hx₁⟩
    rcases hx₂' with ⟨ι₂, hι₂, a₂, b₂, h₂, hx₂⟩
    simp
    use ι₁ ⊕ ι₂, inferInstance
    refine (
      fun i =>
        match i with
        | Sum.inl i₁ => a₁ i₁,
        | Sum.inr i₂ => a₂ i₂,
      ?_
    )


    sorry

  zero_mem' := sorry
  smul_mem' := sorry -/



def prod : Ideal R where
  carrier := prod_carrier I J
  add_mem' := by
    intro x₁ x₂ hx₁ hx₂
    rcases hx₁ with ⟨ι₁, hι₁, a₁, b₁, h₁, hx₁⟩
    rcases hx₂ with ⟨ι₂, hι₂, a₂, b₂, h₂, hx₂⟩
    refine ?_
    refine ⟨ι₁ ⊕ ι₂, inferInstance,
      (fun i =>
        match i with
        | Sum.inl i₁ => a₁ i₁
        | Sum.inr i₂ => a₂ i₂),
      (fun i =>
        match i with
        | Sum.inl i₁ => b₁ i₁
        | Sum.inr i₂ => b₂ i₂),
      ?_⟩
    have h :=
      (Fintype.sum_sum_type
        (fun i : ι₁ ⊕ ι₂ =>
          match i with
          | Sum.inl i₁ => (a₁ i₁ : R) * (b₁ i₁ : R)
          | Sum.inr i₂ => (a₂ i₂ : R) * (b₂ i₂ : R)))
    constructor
    · intro i
      constructor
      · simp
        match i with
        | Sum.inl i₁ =>
          simp
          apply (h₁ i₁).1
        | Sum.inr i₂ =>
          simp
          apply (h₂ i₂).1
      aesop
    simpa [hx₁, hx₂] using h.symm


  zero_mem' := sorry
  smul_mem' := sorry
