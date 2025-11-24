import Mathlib

variable {R} {S} {T} [CommRing R] [CommRing S] [CommRing T]

#find (Ideal ?R) + (Ideal ?R) = _

variable (I J : Ideal R)

def sum : Ideal R where
  carrier := {x | ∃ a b, (a ∈ I) ∧ (b ∈ J) ∧ (x = a + b)}
  add_mem' := by
    rintro x₁ x₂ ⟨a₁, b₁, ha₁, hb₁, hx₁⟩ ⟨a₂, b₂, ha₂, hb₂, hx₂⟩
    use
    simp
  zero_mem' := _
  smul_mem' := _
