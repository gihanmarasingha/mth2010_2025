import Mathlib

/-
A certain subring of a field.
-/

open Function

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

noncomputable def valZ (x : Kˣ) : ℤ :=
  Classical.choose (v.ne_zero_val_int (by exact x.ne_zero))

lemma valZ_spec (x : Kˣ) :
    v.f (x : K) = (v.valZ x : WithTop ℤ) :=
  Classical.choose_spec (v.ne_zero_val_int (x.ne_zero))

lemma valZ_mul (x y : Kˣ) :
    v.valZ (x * y) = v.valZ x + v.valZ y := by
  have h_with : v.f ((x * y : Kˣ) : K)
      = v.f (x : K) + v.f (y : K) := by
    simpa using v.mul_add' (x : K) (y : K)
  have h_with' :
      (v.valZ (x * y) : WithTop ℤ)
        = (v.valZ x : WithTop ℤ) + (v.valZ y : WithTop ℤ) := by
    repeat rw [←valZ_spec]
    assumption
  exact_mod_cast h_with'

lemma one_valZ : v.valZ 1 = 0 := by
  have hf : v.valZ 1 + v.valZ 1 = v.valZ 1 :=
    calc v.valZ 1 + v.valZ 1 = v.valZ (1 * 1) := by rw [valZ_mul]
    _ = v.valZ 1 := by norm_num
  linarith

lemma one_val : v.f (1 : K) = 0 := by
  have h := v.valZ_spec (1 : Kˣ)
  have hz : v.valZ (1 : Kˣ) = 0 := v.one_valZ
  simpa [hz] using h

lemma neg_one_valZ : v.valZ (-1) = 0 := by
  have h : v.valZ 1 = v.valZ (-1) + v.valZ (-1) :=
    calc v.valZ 1 = v.valZ ((-1) * (-1)) := by norm_num
    _ = v.valZ (-1) + v.valZ (-1) := by rw [valZ_mul]
  rw [one_valZ] at h
  linarith

lemma neg_one_val : v.f (-1) = 0 := by
  have h := v.valZ_spec (-1 : Kˣ)
  have hz : v.valZ (-1 : Kˣ) = 0 := v.neg_one_valZ
  simpa [hz] using h

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

lemma val_invZ {x : Kˣ} : v.valZ x⁻¹ = -v.valZ x := by
  have h : 0 = v.valZ x + v.valZ x⁻¹ :=
    calc 0 = v.valZ 1 := by rw [one_valZ]
    _ = v.valZ (x * x⁻¹) := by simp
    _ = v.valZ x + v.valZ x⁻¹ := by rw [valZ_mul]
  linarith

lemma val_inv {x : K} (hnz : x ≠ 0) : v.f x⁻¹ = - v.f x := by
  have h : 0 = v.f x + v.f x⁻¹ :=
    calc 0 = v.f 1 := by rw [one_val]
    _ = v.f (x * x⁻¹) := by rw [mul_inv_cancel₀ hnz]
    _ = v.f x + v.f x⁻¹ := by rw [v.mul_add']
  rcases (ne_zero_val_int v hnz) with ⟨n, hn⟩
  rcases (ne_zero_val_int v (inv_ne_zero hnz)) with ⟨m, hm⟩
  have hnmsump : 0 = (n : WithTop ℤ) + (m : WithTop ℤ) := by
    simpa [hn, hm] using h
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

lemma vring_unit (r : vring v) : (∃ (s : vring v), r * s = 1) ↔ v.f r = 0 := by
  have rnn : v.f r ≥ 0 := r.property
  constructor
  · rintro ⟨s, hs⟩
    have myeq : r.1 * s.1 = 1 := by
      exact_mod_cast hs
    have rnz : r.1 ≠ 0 := by
      intro req
      rw [req, zero_mul] at myeq
      exact zero_ne_one myeq
    have snz : s.1 ≠ 0 := by
      intro seq
      rw [seq, mul_zero] at myeq
      exact zero_ne_one myeq
    rcases (ne_zero_val_int v rnz) with ⟨n, hn⟩
    rcases (ne_zero_val_int v snz) with ⟨m, hm⟩
    have rssum : v.f r + v.f s = 0 :=
      calc v.f r + v.f s = v.f (r * s) := by rw [v.mul_add']
      _ = v.f 1 := by norm_cast; rw [hs]; norm_cast
      _ = 0 := by rw [one_val]
    have nmsump : (n : WithTop ℤ) + m = 0 := by simpa [hn, hm] using rssum
    have nmsum : n + m = 0 := mod_cast nmsump
    have hnnn : n ≥ 0 := by simpa [hn] using rnn
    have hss : v.f s ≥ 0 := s.property
    have hmnn : m ≥ 0 := by simpa [hm] using hss
    have hnzero : n = 0 := by linarith
    simpa [hnzero] using hn
  intro vrzero
  have rnzero : (r :  K) ≠ 0 := by
    by_contra!
    rw [←v.zero_val] at this
    have zeq : (0 : WithTop ℤ) = ⊤ := by
      rw [←vrzero, this]
    exact WithTop.zero_ne_top zeq
  have h_inv0 : v.f ((r : K)⁻¹) = 0 := by
    have h := v.val_inv (x := (r : K)) rnzero
    simpa [vrzero] using h
  have hr_inv_nonneg : v.f ((r : K)⁻¹) ≥ 0 := by simp [h_inv0]
  let rinv : vring v := ⟨(r : K)⁻¹, hr_inv_nonneg⟩
  have h1 : r * rinv = (1 : v.vring) := by
    ext
    simp [rinv, rnzero]
  use rinv


end VFunc
