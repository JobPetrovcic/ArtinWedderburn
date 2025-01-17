import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import ArtinWedderburn.IdealProd

variable {R : Type*} [Ring R] (a b : R)

def left_mul (a : R) : Set R := {x | ∃ r : R, x = r * a}
def right_mul (a : R) : Set R := {x | ∃ r : R, x = a * r}

theorem left_mul_zero_impl_mul_zero : both_mul a b = {0} → a * b = 0 := by
  intro h
  have k : a * b ∈ both_mul a b := by use 1; simp
  rw [h] at k
  exact k

theorem in_particular (a c b : R) : both_mul a b = {0} → a * c * b = 0 := by
  intro h
  have k : a * c * b ∈ both_mul a b := by use c
  rw [h] at k
  exact k

open Pointwise Set

-- aRb = 0 implies Ra = 0 or Rb = 0
theorem both_mul_zero_one_left_zero : both_mul a b = {0} → (left_mul a) * (left_mul b) = {0} := by
  intro h
  apply Set.ext_iff.mpr
  intro x
  constructor
  · rintro ⟨y, ⟨r, hr⟩, z, ⟨s, hs⟩, hx⟩
    simp at hx
    calc
      x = y * z := by rw[← hx]
      _ = (r * a) * (s * b) := by rw [hr, hs]
      _ = r * (a * s * b) := by noncomm_ring
      _ = r * 0 := by rw [in_particular a s b h]
      _ = 0 := by noncomm_ring
  · intro hx
    simp at hx
    use 0
    constructor
    · use 0; noncomm_ring
    · use 0
      constructor
      · use 0; noncomm_ring
      · simp; symm; exact hx

def left_ideal_of_element (a : R) : Ideal R := {
  carrier := left_mul a,
  zero_mem' := by use 0; noncomm_ring,
  add_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r + s
    rw [hr, hs]
    noncomm_ring,
  smul_mem' := by
    rintro x y ⟨r, hr⟩
    use x * r
    rw [hr]
    noncomm_ring
}

theorem carrier_of_left_ideal_of_element (a : R) : (left_ideal_of_element a).carrier = left_mul a := rfl
