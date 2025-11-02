import Mathlib

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

example : f.degree = 1 := by
  apply degree_linear -- The result that a linear polynomial has degree 1
  norm_num

def p : Polynomial ℚ := C 5 * X ^ 2 + C 0 * X + C 3

example : g = p := by
  have h : 5 = ∑ x ∈ Finset.antidiagonal 2, if x.2 = 2 then if x.1 = 0 then 5 else 0 else 0 := by
    decide -- A result concerning the natural number `5` needed in some of the sequell
  ext n
  simp [g, p, coeff_add, coeff_C, coeff_mul]
  split_ifs with h₁ h₂ h₃
  · linarith
  · rw [h₁]
    simp
    exact_mod_cast h
  · rw [h₃]
    simp
  · simp
    have c3 : coeff ((C 3) : ℚ[X]) n = 0 := by
      rw [coeff_C]
      split_ifs
      norm_num
    have c31 : coeff (3 : ℚ[X]) n = 0 := by
      exact_mod_cast c3
    rw [c31]
    have : (if n = 2 then (5 : ℚ) else 0) = 0 := by simp [h₁]
    -- and the sum is 0 because every summand vanishes
    have hzero :
      ∀ x ∈ Finset.antidiagonal n,
        (if x.2 = 2 then if x.1 = 0 then (5 : ℚ) else 0 else 0) = 0 := by
      intro x hx
      rcases x with ⟨i, k⟩
      by_cases hk : k = 2
      · by_cases hi : i = 0
        -- if i=0 and k=2, then i+k = n ⇒ n=2, contradicting hn
        · have : i + k = n := (Finset.mem_antidiagonal.mp hx)
          have : n = 2 := by symm; simpa [hi, hk, add_comm] using this
          exact (h₁ this).elim
        · simp [hk, hi]
      · simp [hk]
    have : (∑ x ∈ Finset.antidiagonal n,
              (if x.2 = 2 then if x.1 = 0 then (5 : ℚ) else 0 else 0)) = 0 := by
      -- sum of zeros over a finite set
      exact Finset.sum_eq_zero hzero
    simp [this]


end section

#min_imports
