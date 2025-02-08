import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Init.Data.Fin.Basic
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import ArtinWedderburn.MatrixUnits
import ArtinWedderburn.Idempotents

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]


-- ALREADY DONE: see MatrixUnits
-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11

-- Finally, the Artin-Wedderburn theorem
universe u

-- kje zahtevamo da je n > 0?
-- kje zahtevamo da je e ≠ 0?
-- Lema OrtIdem -> HasMatrixUnits?
-- Lema HasMatrixUnits -> statement izreka?

def IdemIdeal (I : Ideal R) : Prop := ∃ (e : R), IsIdempotentElem e ∧ I = Ideal.span {e}

def OrtIdem (R : Type u) [Ring R] : Prop := ∃ (n : ℕ) (ι : Fin n → R) (h : (i : Fin n) → IsIdempotentElem (ι i)), (∑ i, ι i = 1) ∧ (∀ i j, IsOrthogonal (ι i) (ι j)) ∧ (∀ i, IsDivisionRing (CornerSubring (h i)))

def NiceIdeal (I : Ideal R) : Prop := IdemIdeal I → ∃ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} ∧ OrtIdem (CornerSubring idem)

def NiceIdeal' (I : Ideal R) : Prop := IdemIdeal I → ∀ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} →  OrtIdem (CornerSubring idem)

lemma corner_nontrivial (R : Type u) [Ring R] {e : R} (idem_e : IsIdempotentElem e) (e_nonzero : e ≠ 0) : Nontrivial (CornerSubring idem_e) := by
  constructor
  use ⟨e, by exact e_in_corner_ring idem_e⟩
  use 0
  exact (nonzero idem_e ⟨e, e_in_corner_ring idem_e⟩).mpr e_nonzero

theorem OrtIdem_HasMatrixUnits (R : Type u) [Ring R] (ort_idem : OrtIdem R) : ∃ (n : ℕ), HasMatrixUnits R n := by sorry

theorem subideals_nice_ideal_nice' [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (h : ∀ J, J < I → NiceIdeal' J) : NiceIdeal' I := by
  intro h_idem_I e enz idem_e I_span_e
  have e_nonzero : e ≠ 0 := by sorry
  have corner_nontriv : Nontrivial (CornerSubring idem_e) := by exact corner_nontrivial R idem_e e_nonzero
  have corner_prime : IsPrimeRing (CornerSubring idem_e) := by exact corner_ring_prime idem_e h_prime
  have corner_artinian : IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by exact corner_ring_artinian idem_e
  obtain ⟨f, ⟨fnz, idem_f, div_f⟩⟩ := prime_and_artinian_esists_idem_corner_div corner_prime corner_artinian
  have fnzR : (f.val : R) ≠ 0 := by exact (nonzero idem_e f).mp fnz

  have idem_one_sub_e : IsIdempotentElem (1 - e) := by exact IsIdempotentElem.one_sub idem_e
  have f_mem : f.val ∈ both_mul e e := by exact Subtype.coe_prop f
  have idem_f_val : IsIdempotentElem f.val := by
    unfold IsIdempotentElem
    calc _ = (f * f).val := by exact rfl
        _ = f.val := by exact congrArg Subtype.val idem_f

  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f := by
    have h' := f_in_corner_othogonal (1- e) f idem_one_sub_e (by simp)
    exact h'

  have ef_eq_f : e * f = f := by exact left_unit_mul idem_e f_mem
  have hfRf : (both_mul f f) = both_mul (f : R) (f : R) := by exact both_mul_lift idem_e f f

  have idem_e_sub_f : IsIdempotentElem (e - f) := by
    unfold IsIdempotentElem
    calc _ = (e * e) - e * f + (f * f) - f * e   := by noncomm_ring
        _ = e - f + f - f * e := by rw [idem_e, ef_eq_f]; sorry
        _ = e - f + f * (1 - e) := by noncomm_ring
        _ = e - f := by rw [one_sub_e_f_orthogonal.2]; noncomm_ring

  let J : Ideal R := Ideal.span {e - f}
  #check J
  have J_sub_I : J < I := by
    rw [I_span_e]
    apply e_span_larger_e_sub_f e f ⟨idem_one_sub_e, idem_f_val, one_sub_e_f_orthogonal⟩ fnzR

  have J_nice := h J J_sub_I
  have J_idem : IdemIdeal J := by use e - f
  specialize J_nice J_idem (e - f) (by sorry) idem_e_sub_f (by rfl)

  unfold OrtIdem at *
  let ⟨n, h, h_idem, h_sum, ⟨h_ort, h_div⟩⟩ := J_nice
  use (n + 1)
  --have h'' : ∀ i, (h i) ∈ CornerSubring idem_e := by sorry

  --have h_sum' : f + ∑ i, h i = 1 := by sorry
  --have h_ort' : ∀ i, IsOrthogonal (h i) f := by sorry
  --have h_div' : ∀ i, IsDivisionRing (CornerSubring (h i)) := by sorry

  --use (λ i =>  if i = n then f else h (Fin.castLT i (by sorry))
  --use (λ i => if i = n then idem_f else h_idem (Fin.castLT i (by sorry)))

  sorry


theorem acc_ideal_nice [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (h_acc : Acc (fun x y => x < y) I) : NiceIdeal' I := by
  induction h_acc with
  | intro J h_acc_J hJ =>
    exact subideals_nice_ideal_nice' h_prime h_art J hJ


def ArtinWedderburnForPrime {R : Type u} [Ring R] [Nontrivial R] (h_prime : IsPrimeRing R) (h_artinian : IsArtinian R R) :
  ∃ (n : ℕ) (D : Type u) ( _ : DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have R_acc : Acc (fun x y => x < y) (⊤ : Ideal R) := by exact IsWellFounded.apply (fun x y ↦ x < y) ⊤
  have R_nice := acc_ideal_nice h_prime h_artinian ⊤ R_acc
  #check IdemIdeal ⊤
  have R_idem : IdemIdeal (⊤ : Ideal R) := by
    use 1
    constructor
    · exact IsIdempotentElem.one
    · exact Eq.symm Ideal.span_singleton_one
  specialize R_nice R_idem 1 (by exact one_ne_zero) IsIdempotentElem.one (by exact Eq.symm Ideal.span_singleton_one)
  unfold OrtIdem at *
  have R_ort_idem : OrtIdem R := by sorry
  have h_matrix_units : ∃(n : ℕ), HasMatrixUnits R n := by exact OrtIdem_HasMatrixUnits R R_ort_idem
  obtain ⟨n, h_matrix_units⟩ := h_matrix_units
      /-
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, IsAtom I := artinian_ring_has_minimal_left_ideal_of_element
  have h_sq_nz : I * I ≠ ⊥ := by
    intro h_sq_zero
    apply h I I at h_sq_zero
    simp at h_sq_zero
    exact hI.1 h_sq_zero
    -/
  sorry -- Leave for now, split into multiple lemmas

def ArtinWedderburnForSimple {R : Type u} [Ring R] [IsSimpleRing R] :
  ∃ (n : ℕ) (D : Type u) ( _ :DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by sorry -- Just an application

-- We can use previous to prove this
proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
    ∃ (n : ℕ) (S : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (S i)),
      Nonempty (R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (S i))





/-

theorem subideals_nice_ideal_nice [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (h : ∀ J, J < I → NiceIdeal J) : NiceIdeal I := by
  intro h_idem_I
  obtain ⟨e, e_nonzero, idem_e, I_span_e⟩ := h_idem_I

  have corner_nontriv : Nontrivial (CornerSubring idem_e) := by exact corner_nontrivial R idem_e e_nonzero
  have corner_prime : IsPrimeRing (CornerSubring idem_e) := by exact corner_ring_prime idem_e h_prime
  have corner_artinian : IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by exact corner_ring_artinian idem_e
  obtain ⟨f, ⟨fnz, idem_f, div_f⟩⟩ := prime_and_artinian_esists_idem_corner_div corner_prime corner_artinian
  have fnzR : (f.val : R) ≠ 0 := by exact (nonzero idem_e f).mp fnz

  have idem_one_sub_e : IsIdempotentElem (1 - e) := by exact IsIdempotentElem.one_sub idem_e
  have f_mem : f.val ∈ both_mul e e := by exact Subtype.coe_prop f
  have idem_f_val : IsIdempotentElem f.val := by
    unfold IsIdempotentElem
    calc _ = (f * f).val := by exact rfl
        _ = f.val := by exact congrArg Subtype.val idem_f

  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f := by
    have h' := f_in_corner_othogonal (1- e) f idem_one_sub_e (by simp)
    exact h'

  have ef_eq_f : e * f = f := by exact left_unit_mul idem_e f_mem
  have hfRf : (both_mul f f) = both_mul (f : R) (f : R) := by exact both_mul_lift idem_e f f


  have idem_e_sub_f : IsIdempotentElem (e - f) := by
    unfold IsIdempotentElem
    calc _ = (e * e) - e * f + (f * f) - f * e   := by noncomm_ring
        _ = e - f + f - f * e := by rw [idem_e, ef_eq_f]; sorry
        _ = e - f + f * (1 - e) := by noncomm_ring
        _ = e - f := by rw [one_sub_e_f_orthogonal.2]; noncomm_ring

  let J : Ideal R := Ideal.span {e - f}
  #check J
  have J_sub_I : J < I := by
    rw [I_span_e]
    apply e_span_larger_e_sub_f e f ⟨idem_one_sub_e, idem_f_val, one_sub_e_f_orthogonal⟩ fnzR

  have J_nice := h J J_sub_I
  have J_idem : IdemIdeal J := by
    use e - f
    constructor
    · sorry
    constructor
    · exact idem_e_sub_f
    · exact rfl
  specialize J_nice J_idem


  obtain ⟨g, idem_g, J_span_g, ⟨n, ι, h_idem, h_sum, h_ort⟩⟩ := J_nice

  use e, idem_e
  constructor
  · exact I_span_e
  · unfold OrtIdem
    use (n + 1)
    --use (λ i =>  if i = n then f else ι (Fin.castLT i (by sorry)))
    --use (λ i => if i = n then idem_f else h_idem (Fin.castLT i (by sorry)))

    sorry
-/


/-
theorem corner_ring_of_ideal_has_matrix_units (I : Ideal R) (h : ∃ (e : R), IsIdempotentElem e ∧  I = Ideal.span {e}) (I_acc : Acc (fun x y => x < y) I) (h_nontriv : Nontrivial R) (h_prime : IsPrimeRing R) (h_artinian : IsArtinian R R): ∃ (n : ℕ), HasMatrixUnits (CornerSubring idem_e) n := by
  induction I_acc with
  | intro J J_acc hJ =>
    let e' := e_idem_to_one_sub_e_idem e idem_e
    have corner_nontriv : Nontrivial (CornerSubring e') := by sorry
    have corner_prime : IsPrimeRing (CornerSubring e') := by exact corner_ring_prime e' h_prime
    have corner_artinian : IsArtinian (CornerSubring e') (CornerSubring e') := by exact corner_ring_artinian e'
    let ⟨f, ⟨f_nonzero, idem_f, div_f⟩⟩ := prime_and_artinian_esists_idem_corner_div corner_prime corner_artinian
    have ef_ort_idem : AreOrthogonalIdempotents e f := by
      --apply f_in_corner_othogonal e f idem_e idem_f (by sorry)
      sorry
    let f_nonzero_R : (f : R) ≠ 0 := by sorry
    #check f
    let g := e + f
    let L := Ideal.span {1 - g}
    have L_sub_J : L < J := by
      rw [h]
      --one_sub_e_larger_span_on_sub_e_sub_f e f  ef_ort_idem f_nonzero_R
      sorry
    specialize hJ L L_sub_J
    --  span_ef_sub_span_e)
    sorry
-/
