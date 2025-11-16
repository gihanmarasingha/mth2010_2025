import Mathlib

/-
A certain subring of a field.
-/

open Function

--structure Subring' (R : Type*) [Ring R] extends AddSubgroup R, Subsemigroup R

structure VFunc (K : Type*) [Field K] where
  f : K → WithTop ℤ
  zero_val : ∀ x, f x = ⊤ ↔ x = 0
  surj' : f.Surjective
  mul_add' : ∀ x y, f (x * y) = f x + f y
  add_ge_min' : ∀ x y, f (x + y) ≥ min (f x) (f y)

namespace VFunc

variable {K} [Field K] (v : VFunc K)

lemma ne_zero_val_int {x : K} (hxnz : x ≠ 0) : ∃ (n : ℤ), v.f x = n := by
  have hne : v.f x ≠ ⊤ := by
    intro h
    rw [v.zero_val] at h
    exact hxnz h
  exact Option.ne_none_iff_exists'.mp hne

lemma one_val : v.f 1 = 0 := by
  rcases (ne_zero_val_int v (one_ne_zero)) with ⟨n, hn⟩
  have hf : v.f 1 + v.f 1 = v.f 1 + 0 :=
    calc v.f 1 + v.f 1 = v.f (1 * 1) := by rw [v.mul_add']
    _ = v.f 1 + 0 := by norm_num
  have hneq : n + n = n + 0 := by
    rw [hn] at hf
    exact_mod_cast hf
  have hnz : n = 0 := by apply add_left_cancel hneq
  rw [hn, hnz]
  norm_num

lemma neg_one_val : v.f (-1) = 0 := by
  have h : v.f 1 = v.f (-1) + v.f (-1) :=
    calc v.f 1 = v.f ((-1) * (-1)) := by norm_num
    _ = v.f (-1) + v.f (-1) := by rw [v.mul_add']
  rw [one_val v] at h
  have hnone : (-1 : K) ≠ 0 := by
    refine neg_ne_zero.mpr ?_
    exact one_ne_zero
  rcases (ne_zero_val_int v hnone) with ⟨n, hn⟩
  have hnsum : 0 = n + n := by
    rw [hn] at h
    exact_mod_cast h
  have hnz : n = 0 := by
    linarith
  rw [hn]
  exact_mod_cast hnz

lemma neg_val {x : K} : v.f (-x) = v.f x := by
  calc v.f (-x ) = v.f ((-1) * x) := by norm_num
    _ = v.f (-1) + v.f x := by rw [v.mul_add']
    _ = 0 + v.f x := by rw [neg_one_val]
    _ = v.f x := by rw [zero_add]


def vring : Subring K where
  carrier := {x : K | v.f (x : K) ≥ 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at * -- Find this from `simp?`
    rw [v.mul_add']
    exact Left.add_nonneg ha hb -- Find via `apply?`
  one_mem' := by
    show v.f 1 ≥ 0
    rw [one_val]
  add_mem' := by
    intro a b (ha : v.f a ≥ 0) (hb : v.f b ≥ 0)
    show v.f (a + b) ≥ 0
    calc v.f (a + b) ≥ min (v.f a) (v.f b) := by apply v.add_ge_min'
    _ ≥ 0 := by exact le_min ha hb -- Found using `apply?`
  zero_mem' := by
    show v.f 0 ≥ 0
    have hz : v.f (0 : K) = ⊤ := by rw [v.zero_val]
    rw [hz]
    exact OrderTop.le_top 0
  neg_mem' := by
    intro a (ha : v.f a ≥ 0)
    show v.f (-a) ≥ 0
    have h : -a = (-1) * a := by exact neg_eq_neg_one_mul a
    rw [h]
    rw [v.mul_add']
    rw [neg_one_val, zero_add]
    exact ha

lemma val_inv {x : K} (hnz : x ≠ 0) : v.f x⁻¹ = - v.f x := by
  have h : 0 = v.f x + v.f x⁻¹ :=
    calc 0 = v.f 1 := by rw [one_val]
    _ = v.f (x * x⁻¹) := by rw [mul_inv_cancel₀ hnz]
    _ = v.f x + v.f x⁻¹ := by rw [v.mul_add']
  rcases (ne_zero_val_int v hnz) with ⟨n, hn⟩
  rcases (ne_zero_val_int v (inv_ne_zero hnz)) with ⟨m, hm⟩
  have hnmsump : 0 = (n : WithTop ℤ) + (m : WithTop ℤ) := by
    rw [←hn, ←hm, h]
  have hnmsum : 0 = n + m := by
    exact_mod_cast hnmsump
  have hmneg : m = -n := by linarith
  rw [hm, hn, hmneg]
  norm_cast

lemma mem_or_inv_mem (x : K) (h : x ≠ 0) : x ∈ (vring v).carrier ∨ x⁻¹ ∈ (vring v).carrier := by
  rw [or_iff_not_imp_left]
  intro hxnot
  show v.f x⁻¹ ≥ 0
  contrapose! hxnot
  show v.f x ≥ 0
  rw [val_inv v h] at hxnot
  rcases (ne_zero_val_int v h) with ⟨n, hn⟩
  have h1t : -(n : WithTop ℤ) < 0 := by rwa [←hn]
  have h1 : -n < 0 := by exact_mod_cast h1t
  have h2 : n ≥ 0 := by linarith
  have h2t : (n : WithTop ℤ) ≥ 0 := by exact_mod_cast h2
  rwa [hn]

/- lemma vring_unit {r : K} (hr : r ∈ vring v) : IsUnit r ↔ v.f r = 0 := by
  change v.f r ≥ 0 at hr
  constructor
  · rintro ⟨y, hy⟩
    have hynn : v.f y ≥ 0 := by rwa [hy]
    have hinvsum : v.f y + v.f y⁻¹ = 0 := by

      sorry

    sorry
  sorry -/


end VFunc
