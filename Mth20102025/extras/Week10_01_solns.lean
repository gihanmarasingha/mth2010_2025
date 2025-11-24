import Mathlib

variable {R} [CommRing R] [DecidableEq R]

variable (I J : Ideal R)

/-
# Sums and products of ideals

Our goal is to prove that if `I` and `J` are ideals of a ring `R`, then so are
`I + J` and `I * J`.

Here,

  `I + J = {a + b | a ∈ I and b ∈ J}`

and

  `I * J = {∑ᵢ aᵢ * bᵢ : aᵢ ∈ I and bᵢ ∈ J}`

where the sum is over a finite set.
-/

/-
## Using ideal properties

Here are the three main properties that define an ideal and how to use them.
-/

example : 0 ∈ I := by apply zero_mem

example {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by apply add_mem hx hy

example {x r : R} (hx : x ∈ I) : r * x ∈ I := by apply Ideal.mul_mem_left _ _ hx

/-
## Sum of ideals

The carrier of the sum of `I` and `J` is the set

  `{x | ∃ a ∈ I, ∃ b ∈ J, x = a + b}`

of elements of `R`.

It remains to show this set contains `0` and is closed under addition and
under multiplication on the left by elements of `R`.
-/

@[simp]
def sum_set : Set R :=  {x | ∃ a ∈ I, ∃ b ∈ J, x = a + b}

def sum : Ideal R where
  carrier := sum_set I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ sum_set I J → x₂ ∈ sum_set I J → x₁ + x₂ ∈ sum_set I J
    intro x₁ x₂ hx₁' hx₂'
    rcases hx₁' with ⟨a₁, ha₁, b₁, hb₁, hx₁⟩
    rcases hx₂' with ⟨a₂, ha₂, b₂, hb₂, hx₂⟩
    simp
    use a₁ + a₂, ?_, b₁ + b₂, ?_
    · rw [hx₁, hx₂]
      ring
    · apply add_mem ha₁ ha₂
    apply add_mem hb₁ hb₂ -- sorry
  zero_mem' := by
    show 0 ∈ sum_set I J
    simp
    use 0, ?_, 0, ?_ -- sorry copy the `use` above
    all_goals simp
  smul_mem' := by
    show ∀ r x, x ∈ sum_set I J → r * x ∈ sum_set I J
    rintro r x hx'
    rcases hx' with ⟨a, ha, b, hb, hx⟩
    simp
    rw [hx]
    use r * a, ?_, r * b, ?_
    · ring
    · apply Ideal.mul_mem_left _ _ ha
    apply Ideal.mul_mem_left _ _ hb

/-
## Products of ideals
-/

@[simp]
def prod_set : Set R :=
  {x | ∃ (ι : Type*) (_ : Fintype ι)
        (a b : ι → R),
        (∀ i, a i ∈ I ∧ b i ∈ J) ∧
        x = ∑ i, a i * b i }


def prod : Ideal R where
  carrier := prod_set I J
  add_mem' := by
    intro x₁ x₂ hx₁' hx₂'
    rcases hx₁' with ⟨ι₁, hι₁, a₁, b₁, h₁, hx₁⟩
    rcases hx₂' with ⟨ι₂, hι₂, a₂, b₂, h₂, hx₂⟩
    use ι₁ ⊕ ι₂, inferInstance
    use fun i =>
        match i with
        | Sum.inl i₁ => a₁ i₁
        | Sum.inr i₂ => a₂ i₂
    use fun i =>
        match i with
        | Sum.inl i₁ => b₁ i₁
        | Sum.inr i₂ => b₂ i₂
    constructor
    · intro i
      constructor
      · match i with
        | Sum.inl i₁ =>
          simp
          apply (h₁ i₁).1
        | Sum.inr i₂ =>
          simp
          apply (h₂ i₂).1
      match i with
      | Sum.inl i₁ =>
          simp
          apply (h₁ i₁).2
      | Sum.inr i₂ =>
          simp
          apply (h₂ i₂).2
    simp [hx₁, hx₂]
  zero_mem' := by
    use Unit, inferInstance
    use fun i => 0
    use fun i => 0
    constructor
    · simp
    simp
  smul_mem' := by
    intro r x hx'
    rcases hx' with ⟨ι, hι, a, b, h, hx⟩
    use ι, inferInstance
    use fun i => r * (a i)
    use b
    constructor
    · intro i
      constructor
      · have ha : a i ∈ I := (h i).1
        apply Ideal.mul_mem_left _ _ ha
      have hb : b i ∈ J := (h i).2
      exact hb
    rw [hx]
    calc r * ∑ i, a i * b i = ∑ i, r * (a i * b i) := by simp [Finset.mul_sum]
      _ = ∑ i, (r * a i) * b i := by simp [mul_assoc]
