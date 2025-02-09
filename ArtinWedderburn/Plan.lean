import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Init.Data.Fin.Basic
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import ArtinWedderburn.MatrixUnits
import ArtinWedderburn.Idempotents
import ArtinWedderburn.NiceIdeals

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]


-- ALREADY DONE: see MatrixUnits
-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11

-- Finally, the Artin-Wedderburn theorem
universe u


set_option pp.proofs true

def ArtinWedderburnForPrime {R : Type u} [Ring R] [Nontrivial R] (h_prime : IsPrimeRing R) (h_artinian : IsArtinian R R) :
  ∃ (n : ℕ) (D : Type u) ( _ : DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have R_acc : Acc (fun x y => x < y) (⊤ : Ideal R) := by exact IsWellFounded.apply (fun x y ↦ x < y) ⊤
  have R_nice := acc_ideal_nice h_prime h_artinian ⊤ R_acc
  have R_idem : IdemIdeal (⊤ : Ideal R) := by
    use 1
    constructor
    · exact IsIdempotentElem.one
    · exact Eq.symm Ideal.span_singleton_one
  specialize R_nice R_idem 1 IsIdempotentElem.one (by exact Eq.symm Ideal.span_singleton_one)

  unfold OrtIdem at *
  have R_ort_idem : OrtIdemDiv R := by
    have top_nice : NiceIdeal (⊤ : Ideal R) := by
      apply acc_ideal_nice
      exact h_prime
      exact h_artinian
      exact R_acc
    have top_idem : IdemIdeal (⊤ : Ideal R) := by
      use 1
      constructor
      exact IsIdempotentElem.one
      exact Eq.symm Ideal.span_singleton_one
    specialize top_nice top_idem 1 IsIdempotentElem.one (Eq.symm Ideal.span_singleton_one)

    sorry
  let ⟨e, idem_e, n, ⟨h_div, h_iso⟩⟩ := lemma_2_20_full R h_prime R_ort_idem
  use n, (CornerSubring idem_e)
  use IsDivisionRing_to_DivisionRing h_div



def ArtinWedderburnForSimple {R : Type u} [Ring R] [IsSimpleRing R] :
  ∃ (n : ℕ) (D : Type u) ( _ :DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by sorry -- Just an application

-- We can use previous to prove this
proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
    ∃ (n : ℕ) (S : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (S i)),
      Nonempty (R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (S i))
