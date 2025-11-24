import Mathlib

/-
# A question about maximal ideals

Let `I = (5, 1 + √11)` in the ring `R = ℤ[√11]`.

Show that `I` is a maximal ideal of `R`.
-/

/-
In Mathlib, `ℤ√d` is the ring `ℤ[√d]`. Thus, `ℤ√2` is `ℤ[√2]`. This is an
abbreviation for `Zsqrtd`
-/

abbrev R := ℤ√11

def sqrt11 : R := Zsqrtd.sqrtd

notation "√11" => sqrt11

namespace Z11calculations

def a : R := 5 + 3 * √11

def b : R := 1 + 2 * √11

/-
# Exercise:

Replace the `sorry`s in brackets below with numbers and the `by sorry` with
`by rfl`.

Note, you can also get Lean to perform the calculation by using

`#eval a + b` or `#eval a * b`.
-/

example : a + b = ⟨sorry, sorry⟩ := by sorry

example : a * b = ⟨sorry, sorry⟩ := by sorry

end Z11calculations

def I : Ideal R := Ideal.span {5, 1 + √11}

abbrev F := ZMod 5

local instance : Fact (Nat.Prime 5) := by decide

#check RingHom.ker_isMaximal_of_surjective

def φ : R → F := by
  rintro ⟨a, b⟩
  exact a - b

#eval φ (4 + 3 * √11)

lemma eleven_eq_one : (11 : F) = (1 : F) := by decide

def f : R →+* F where
  toFun := φ
  map_one' := by
    simp [φ]
  map_mul' := by
    intro a b
    simp [φ, eleven_eq_one]
    ring
  map_zero' := by
    simp [φ]
  map_add' := by
    intro a b
    simp [φ]
    ring

lemma ker_sub_I : RingHom.ker f ≤ I := by
  rintro ⟨a, b⟩ hx
  change (f ⟨a, b⟩) = 0 at hx
  dsimp [f, φ] at hx
  norm_cast at hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_def] at hx
  rcases hx with ⟨c, hc⟩
  norm_cast at hc
  have ha : a = 5 * c + b := by
    linarith
  rw [I, Ideal.mem_span_pair]
  use c, b
  rw [ha]
  ext
  · simp
    have h1 : 1 + √11.re = (1 : ℤ) := by decide
    rw [h1]
    ring
  · simp
    have h1 : √11.im = (1 : ℤ) := by decide
    rw [h1]
    ring

lemma I_sub_ker : I ≤ RingHom.ker f := by
  intro r hr
  rw [I, Ideal.mem_span_pair] at hr
  rcases hr with ⟨a, b, rfl⟩
  change f (a * 5 + b * (1 + √11)) = 0
  dsimp [f, φ]
  simp
  have h1 : 1 + √11.re = (1 : F) := by decide
  have h2 : √11.im = (1 : F) := by decide
  have h3 : (11 : F) = 1 := by decide
  have h4 : (5 : F) = 0 := by decide
  rw [h1, h2, h3, h4]
  ring

lemma ker_eq_I : RingHom.ker f = I := by
  apply le_antisymm
  · exact ker_sub_I
  · exact I_sub_ker

lemma surjective_f : Function.Surjective f := by
  rintro z
  use Zsqrtd.ofInt z.val
  simp

example : I.IsMaximal := by
  rw [←ker_eq_I]
  apply RingHom.ker_isMaximal_of_surjective
  exact surjective_f
