import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
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

def IdemIdeal (I : Ideal R) : Prop := ∃ (e : R), IsIdempotentElem e ∧  I = Ideal.span {e}

def OrtIdem (R : Type u) [Ring R] : Prop := ∃ (n : ℕ) (ι : Fin n → R) , ∀ i, IsIdempotentElem (ι i) ∧  (∑ i, ι i = 1) ∧ ∀ i j, IsOrthogonal (ι i) (ι j)

def NiceIdeal (I : Ideal R) : Prop := IdemIdeal I → ∃ (e : R) (idem : IsIdempotentElem e), Ideal.span {e} = I ∧ OrtIdem (CornerSubring idem) ∧ IsDivisionRing (CornerSubring idem)

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

def ArtinWedderburnForPrime {R : Type u} [Ring R] [Nontrivial R] (h : IsPrimeRing R) [IsArtinian R R] :
    ∃ (n : ℕ) (D : Type u) ( _ : DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, IsAtom I := artinian_ring_has_minimal_left_ideal_of_element
  have h_sq_nz : I * I ≠ ⊥ := by
    intro h_sq_zero
    apply h I I at h_sq_zero
    simp at h_sq_zero
    exact hI.1 h_sq_zero
  sorry -- Leave for now, split into multiple lemmas

def ArtinWedderburnForSimple {R : Type u} [Ring R] [IsSimpleRing R] :
  ∃ (n : ℕ) (D : Type u) ( _ :DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by sorry -- Just an application

-- We can use previous to prove this
proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
    ∃ (n : ℕ) (S : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (S i)),
      Nonempty (R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (S i))
