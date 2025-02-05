import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
<<<<<<< HEAD
import ArtinWedderburn.CornerRing
import ArtinWedderburn.MatrixUnits
=======
--import ArtinWedderburn.MatrixUnits
--import ArtinWedderburn.CornerRing
>>>>>>> ba83987431ef160a7c69624ec6cb1a9a2b85711a

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]

variable (I J : Ideal R) -- Ideals in mathlib are LEFT ideals (defined as Submodule R R)

variable (A B C: Set R)



variable (e : R)
variable (idem_e : IsIdempotentElem e)


-- ALREADY DONE: see MatrixUnits
-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11

-- Finally, the Artin-Wedderburn theorem
universe u

def corner_ring_of_ideal_has_matrix_units (I : Ideal R) (idem_e : IsIdempotentElem e) (h : I = Ideal.span {e}) : ∃ (n : ℕ), HasMatrixUnits (CornerSubring idem_e) n := by sorry

def ArtinWedderburnForPrime {R : Type u} [Ring R] (h : IsPrimeRing R) [IsArtinian R R] :
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
