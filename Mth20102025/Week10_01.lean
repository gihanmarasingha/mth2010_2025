import Mathlib

variable {R} [CommRing R] [DecidableEq R]

variable (I J : Ideal R)

/-
# Sums and products of ideals

Your goal is to prove that if `I` and `J` are ideals of a ring `R`, then so are
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
Remember you can use `ring` to prove equations involving a ring.
-/

example (a b r : R) : r * (a + b) = r * a + r * b := by ring

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

namespace sum_example

open Submodule

/-
## A sum set example

Below, we define the principal ideals `I₁ = (2)` and `I₂ = (3)` of `ℤ`. One
can see that `1 ∈ I₁ + I₂` as `1 = 2 * 2 + 3 * (-1)`.
-/

def I₁ : Ideal ℤ := span ℤ {2}

def I₂ : Ideal ℤ := span ℤ {3}

example : 1 ∈ sum_set I₁ I₂ := by
  dsimp [sum_set]
  use 4, ?_, (-3), ?_ -- remains to show `1 = 4 - 3`, `4 ∈ I₁` and `-3 ∈ I₂`
  · show 1 = 4 + -3; simp
  · show 4 ∈ I₁
    simp [I₁]
    rw [Ideal.mem_span_singleton]
    norm_num
  show -3 ∈ I₂
  simp [I₂]
  rw [Ideal.mem_span_singleton]

/-
### Exercise

Adapt the above to show that `1 ∈ J₁ + J₂`, where `J₁ = (5)` and `J₂ = (7)`.
-/

def J₁ : Ideal ℤ := span ℤ {5}

def J₂ : Ideal ℤ := span ℤ {7}

example : 1 ∈ sum_set J₁ J₂ := by
  sorry

end sum_example

/-
### Exercise

Finish the proof that `I + J` is an ideal.
-/

def sum : Ideal R where
  carrier := sum_set I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ sum_set I J → x₂ ∈ sum_set I J → x₁ + x₂ ∈ sum_set I J
    intro x₁ x₂ hx₁' hx₂'
    -- Here `hx₁' : x₁ ∈ sum_set I J` and `hx₂' : x₂ ∈ sum_set I J`.
    rcases hx₁' with ⟨
      a₁ : R,
      ha₁ : a₁ ∈ I,
      b₁ : R,
      hb₁ : b₁ ∈ J,
      hx₁ : x₁ = a₁ + b₁
    ⟩
    rcases hx₂' with ⟨a₂, ha₂, b₂, hb₂, hx₂⟩
    --
    show x₁ + x₂ ∈ sum_set I J
    use a₁ + a₂
    constructor
    · show a₁ + a₂ ∈ I
      apply add_mem ha₁ ha₂
    sorry
  zero_mem' := by
    show 0 ∈ sum_set I J
    show ∃ a ∈ I, ∃ b ∈ J, 0 = a + b
    use 0
    constructor
    · show 0 ∈ I; simp
    sorry
  smul_mem' := by
    show ∀ r x, x ∈ sum_set I J → r * x ∈ sum_set I J
    rintro r x hx'
    rcases hx' with ⟨a, ha, b, hb, hx⟩
    show r * x ∈ sum_set I J
    rw [hx]
    sorry

/-
## Products of ideals

### Exercise

Finish the proof that `I * J` is an ideal
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
    rcases hx₁' with ⟨
      ι₁, -- A type.
      _ : Fintype ι₁, -- Proof that `ι₁` is finite.
      a₁ : ι₁ → R, -- A sequence of elements of `R`, indexed by `ι₁`
      b₁ : ι₁ → R,
      h₁ : ∀ (i : ι₁), (a₁ i ∈ I) ∧ (b₁ i ∈ J),
      hx₁ : x₁ = ∑ i, (a₁ i) * (b₁ i)
    ⟩
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
      sorry -- adapt the `match` proof above.
    simp [hx₁, hx₂]
  zero_mem' := by
    use Unit, inferInstance
    sorry
  smul_mem' := by
    intro r x hx'
    rcases hx' with ⟨ι, hι, a, b, h, hx⟩
    use ι, inferInstance
    use sorry
    use sorry
    constructor
    · intro i
      constructor
      · sorry
      sorry
    sorry
