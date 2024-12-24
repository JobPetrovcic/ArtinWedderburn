import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing


variable {R : Type*} [Ring R]
variable (I J : Ideal R)
variable {e f : R}


def IsOrthogonal (e f : R) : Prop := e * f = 0 ∧ f * e = 0

def AreOrthogonalIdempotents (e f : R) : Prop := IsIdempotentElem e ∧ IsIdempotentElem f ∧ IsOrthogonal e f


theorem leq_neq_lt (I J : Ideal R) : I ≤ J → I ≠ J → I < J := by -- Done by Matevz
  intro hleq hneq
  constructor
  · exact hleq
  · intro heq
    have h : I = J := by exact le_antisymm hleq heq
    trivial

-- Lemma 2.9
-- #HARDER
theorem one_sub_e_larger_span_on_sub_e_sub_f (e f : R) (ef_ort_idem : AreOrthogonalIdempotents e f) (fnz : f ≠ 0) : Ideal.span {1 - e - f} < Ideal.span {1 - e} := by -- Done by Matevz
  have hleq : Ideal.span {1 - e - f} ≤ Ideal.span {1 - e} := by
    apply Ideal.span_le.mpr
    intro x hx
    simp at hx
    rw [hx]
    simp
    have factor : (1 - e - f) * (1 - e) = 1 - e - f := by calc
      (1 - e - f) * (1 - e) = 1 - e - f - e + (e * e) + (f * e) := by noncomm_ring
      _ = 1 - e - f - e + e + 0 := by rw [ef_ort_idem.left, ef_ort_idem.right.right.right]
      _ = 1 - e - f := by noncomm_ring
    rw [Eq.symm factor]
    have in_span : 1 - e ∈ Ideal.span {1 - e} := by exact Ideal.mem_span_singleton_self (1 - e)
    exact Ideal.mul_mem_left (Ideal.span {1 - e}) (1 - e - f) in_span
  have hneq : Ideal.span {1 - e - f} ≠ Ideal.span {1 - e} := by
    intro heq
    have f_in_ideal : f ∈ Ideal.span {1 - e} := by
      have fact_f : f = f * (1 - e) := by calc
        f = f - f * e := by rw [ef_ort_idem.right.right.right]; noncomm_ring
        _ = f * (1 - e) := by noncomm_ring
      rw [fact_f]
      exact Ideal.mul_mem_left (Ideal.span {1 - e}) f (Ideal.mem_span_singleton_self (1 - e))
    rw [← heq] at f_in_ideal
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp f_in_ideal
    have fz : f = 0 := by calc
      f = r * (1 - e - f) := by rw [hr]
      _ = r * (1 - e - f - f + e * f + f * f) := by rw [ef_ort_idem.right.right.left, ef_ort_idem.right.left]; noncomm_ring
      _ = r * (1 - e - f) * (1 - f) := by noncomm_ring
      _ = f - f * f := by rw [hr]; noncomm_ring
      _ = 0 := by rw[ef_ort_idem.right.left]; noncomm_ring
    contradiction
  exact leq_neq_lt (Ideal.span {1 - e - f}) (Ideal.span {1 - e}) hleq hneq
