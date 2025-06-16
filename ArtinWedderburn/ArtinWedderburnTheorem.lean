import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Init.Data.Fin.Basic
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import ArtinWedderburn.MatrixUnits
import ArtinWedderburn.Idempotents
import ArtinWedderburn.NiceIdeals
import ArtinWedderburn.Auxiliary

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]


-- ALREADY DONE: see MatrixUnits
-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11

-- Finally, the Artin-Wedderburn theorem
universe u



set_option pp.proofs true

theorem ArtinWedderburnForPrime {R : Type u} [Ring R] [h_nontriv : Nontrivial R] (h_prime : IsPrimeRing R) (h_artinian : IsArtinian R R) :
  ∃ (n : ℕ) (D : Type u) ( _ : DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by -- Maša
  have top_acc : Acc (fun x y => x < y) (⊤ : Ideal R) := by exact IsWellFounded.apply (fun x y ↦ x < y) ⊤
  have top_nice := acc_ideal_nice h_prime h_artinian ⊤ top_acc
  have top_idem : IdemIdeal (⊤ : Ideal R) := by
    use 1
    constructor
    · exact IsIdempotentElem.one
    · exact Eq.symm Ideal.span_singleton_one
  unfold OrtIdem at *
  have R_ort_idem : OrtIdemDiv R := by
    specialize top_nice top_idem 1 IsIdempotentElem.one (Eq.symm Ideal.span_singleton_one)
    apply isomorphic_OrtIdemDiv (iso_corner_one)
    exact top_nice
  have n_pos : 0 < R_ort_idem.n := by exact nontrivial_ortidem_n_pos R h_nontriv R_ort_idem
  let ⟨mu, h⟩ := lemma_2_20' R h_prime R_ort_idem n_pos
  use R_ort_idem.n, (CornerSubring (R_ort_idem.h ⟨0, n_pos⟩)), (IsDivisionRing_to_DivisionRing (R_ort_idem.div ⟨0,n_pos⟩))
  apply Nonempty.intro
  have iso := ring_with_matrix_units_isomorphic_to_matrix_ring R R_ort_idem.n n_pos mu
  unfold e00_cornerring at iso
  unfold CornerSubring at iso ⊢
  apply iso.trans
  apply equal_el_iso_matrix_rings
  unfold IsIdempotentElem
  exact mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, n_pos⟩ ⟨0, n_pos⟩ ⟨0, n_pos⟩ ⟨0, n_pos⟩
  exact R_ort_idem.h  ⟨0, n_pos⟩
  exact h


-- Just an application
theorem ArtinWedderburnForSimple {R : Type u} [Ring R] [IsSimpleRing R] [h_art : IsArtinian R R]:
  ∃ (n : ℕ) (D : Type u) ( _ :DivisionRing D), Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by --Maša
  apply ArtinWedderburnForPrime
  exact simple_ring_is_prime
  exact h_art



-- We can use previous to prove this
proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
    ∃ (n : ℕ) (S : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (S i)),
      Nonempty (R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (S i))
