import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import ArtinWedderburn.SetProd
import ArtinWedderburn.MinIdeals


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






def HasMatrixUnits (R : Type*) [Ring R] (n : ℕ) : Prop := ∃ (es : Fin n → Fin n → R), (∑ i, es i i = 1) ∧ (∀ i j k l, es i j * es k l = (if j = k then es i l else 0)) -- Done by Job (as class - see above) and rewritten by Matevz (as def)

-- just a test to see how the matrices work
theorem TestMatrixUnits (n : ℕ) : HasMatrixUnits (Matrix (Fin 2) (Fin 2) R) 2 := by
  use fun i j => (fun i' j' => if i = i' ∧ j = j' then 1 else 0)
  constructor
  · apply Matrix.ext_iff.mp
    intro i j
    simp
    split_ifs with h1 h2 h3
    · by_contra h
      have h1' := h1.left
      have h2' := h2.left
      rw [← h2'] at h1'
      trivial
    · rw [← h1.left, ← h1.right]
      simp
    · rw [← h3.left, ← h3.right]
      simp
    · sorry
  · sorry




variable (e : R)
variable (idem_e : IsIdempotentElem e)



def kronecker_delta (n : ℕ) (i j : Fin n) : R :=
  if i = j then 1 else 0



-- Lemma 2.18
-- hypothesis: we have a parwise orthogonal idempotent e_ii for each i in {1, ..., n}
-- and e1i ∈ e11Reii for all i in {2, ..., n}
-- and e1iei1 = e11 and ei1e1i = eii for all i in {2, ..., n}
-- conclusion: has matrix units R

def PairwiseOrthogonal (a b : R) : Prop := a * b = 0 ∧ b * a = 0

theorem OrtIdem_imply_MatUnits {n : ℕ} (hn : 0 < n) -- Done by Matevz
  (diag_es : Fin n → R)
  (idem : (∀ i : Fin n, IsIdempotentElem (diag_es i))) -- idempotent
  (ort : (∀ i j : Fin n, i ≠ j → PairwiseOrthogonal (diag_es i) (diag_es j))) -- pairwise orthogonal
  (sum_eq_one : ∑ i, diag_es i = 1) -- sum of diagonal elements is 1
  -- first row
  (row_es : Fin n -> R)
  (row_in : ∀ i : Fin n, row_es i ∈ both_mul (diag_es ⟨0, hn⟩) (diag_es i))
  -- first column
  (col_es : Fin n -> R)
  (col_in : ∀ i : Fin n, col_es i ∈ both_mul (diag_es i) (diag_es ⟨0, hn⟩))
  -- they are compatible
  (comp1 : ∀ i, row_es i * col_es i = diag_es ⟨0, hn⟩)
  (comp2 : ∀ i, col_es i * row_es i = diag_es i)
  : HasMatrixUnits R n := by
  use fun i j => (col_es i) * (row_es j)
  constructor
  · simp_rw [comp2]
    exact sum_eq_one
  · intro i j k l
    split_ifs with h
    · rw [h]
      have col_mul_diag : col_es i * diag_es ⟨0, hn⟩ = col_es i := by
        obtain ⟨r, hr⟩ := col_in i
        calc
          col_es i * diag_es ⟨0, hn⟩ = diag_es i * r * (diag_es ⟨0, hn⟩ * diag_es ⟨0, hn⟩) := by rw [hr]; noncomm_ring
          _ = diag_es i * r * diag_es ⟨0, hn⟩ := by rw [idem ⟨0, hn⟩]
          _ = col_es i := by rw [hr]
      calc
        (col_es i * row_es k) * (col_es k * row_es l) = col_es i * (row_es k * col_es k) * row_es l := by noncomm_ring
        _ = col_es i * diag_es ⟨0, hn⟩ * row_es l := by rw [comp1 k]
        _ = col_es i * row_es l := by rw [col_mul_diag]
    · obtain ⟨r, hr⟩ := row_in j
      obtain ⟨s, hs⟩ := col_in k
      calc
        (col_es i * row_es j) * (col_es k * row_es l) = col_es i * (diag_es ⟨0, hn⟩ * r * (diag_es j * diag_es k) * s * diag_es ⟨0, hn⟩) * row_es l := by rw [hr, hs]; noncomm_ring
        _ = 0 := by rw [(ort j k h).left]; noncomm_ring



-- Lemma 2.19 (a)
theorem lemma_2_19
  (h : IsPrimeRing R)
  (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (ort : IsOrthogonal e f)
  (heRe : IsDivisionRing (CornerSubring idem_e)) (hfRf : IsDivisionRing (CornerSubring idem_f)) :
  ∃ u v : R, u ∈ both_mul e f ∧ v ∈ both_mul f e ∧ u * v = e ∧ v * u = f := by
  sorry
