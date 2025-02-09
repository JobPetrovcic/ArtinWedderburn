import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents

variable {R : Type*} [Ring R]

def IsDivisionSubring (S : NonUnitalSubring R) (e : R) : Prop := (∃ x : R, x ∈ S ∧ x ≠ 0) ∧ (∀ x : R, x ∈ S → x ≠ 0 → ∃ y : R, y ∈ S ∧ y * x = e) -- Done by Matevz

def IsDivisionRing (R : Type*) [Ring R] : Prop := (∃ x : R, x ≠ 0) ∧ (∀ x : R, x ≠ 0 → ∃ y : R, y * x = 1 ∧ x * y = 1) -- Done by Matevz

-- If at some point we decide to define division ring as a ring in which every nonzero element has a two sided inverse
theorem left_inv_implies_divring [Nontrivial R] (h : ∀ x : R, x ≠ 0 → ∃ y : R, y * x = 1) : IsDivisionRing R := by -- Maša
  unfold IsDivisionRing
  constructor
  · exact exists_ne 0
  · intro x x_nz
    let ⟨y, hy⟩ := h x x_nz
    have y_nz : y ≠ 0 := by exact left_ne_zero_of_mul_eq_one hy
    let ⟨z, hz⟩ := h y y_nz
    have x_eq_z : x = z := by
      calc x = (z * y) * x := by rw [hz]; noncomm_ring
          _ = z * (y * x) := by noncomm_ring
          _ = z := by rw [hy]; noncomm_ring
    use y
    constructor
    · exact hy
    · rw [x_eq_z]
      exact hz

noncomputable
def IsDivisionRing_to_DivisionRing (div : IsDivisionRing R) : DivisionRing R := by --Maša
  unfold IsDivisionRing at div
  have nontriv : Nontrivial R := by
    let ⟨⟨x, hx⟩, _⟩ := div
    use x, 0
  apply DivisionRing.ofIsUnitOrEqZero
  intro a
  rw [isUnit_iff_exists]
  let ⟨_, h⟩ := div
  by_cases ha : a = 0
  right
  exact ha
  left
  specialize h a ha
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := h
  use y


theorem isomorphic_ring_div {R' : Type*} [Ring R'] (f : R ≃+* R') (h_div : IsDivisionRing R) : IsDivisionRing R' := by --Maša
  unfold IsDivisionRing at *
  let ⟨⟨x, hx⟩, h⟩ := h_div
  let ⟨y, hy⟩ := h x hx
  constructor
  use f x
  · rw [RingEquiv.map_ne_zero_iff]
    exact hx
  · intro x' hx'
    let ⟨a, ha⟩ : ∃(a : R), f a = x' := by
      use f.symm x'
      exact f.right_inv x'
    let ⟨b, hb⟩ := h a (by rw [← ha] at hx'; exact (RingEquiv.map_ne_zero_iff f).mp hx')
    use f b
    rw [← ha]
    constructor
    · rw [map_mul_eq_one]
      exact hb.1
    . rw [map_mul_eq_one]
      exact hb.2
