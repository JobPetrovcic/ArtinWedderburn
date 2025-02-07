import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Init.Data.Fin.Basic
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import Mathlib.Algebra.Group.Basic
--import ArtinWedderburn.MatrixUnits
import ArtinWedderburn.Idempotents

import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Ring.Defs

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]
universe u

def IdemIdeal (I : Ideal R) : Prop := ∃ (e : R), IsIdempotentElem e ∧ I = Ideal.span {e}

lemma idem_lift_is_idem {e : R} {idem_e : IsIdempotentElem e} (f : CornerSubring idem_e)(hf : IsIdempotentElem f) : IsIdempotentElem (f : R) := by
  unfold IsIdempotentElem at *
  nth_rewrite 3 [←hf]
  rfl

--def OrtIdemDiv (R : Type u) [Ring R] : Prop := OrtIdem R  ∧ (∀ i, IsDivisionRing (CornerSubring (h i)))
--def NiceIdeal' (I : Ideal R) : Prop := IdemIdeal I → ∃ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} ∧ OrtIdem (CornerSubring idem)

def NiceIdeal (I : Ideal R) := IdemIdeal I → ∀ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} →  OrtIdemDiv (CornerSubring idem) -- Maša

def zero_ideal_nice : NiceIdeal (⊥ : Ideal R) := by -- Maša and Matevz
  intro IdemIdeal_zero e idem_e h
  have e_zero : e = 0 := by
    rw [← Ideal.span_singleton_eq_bot]
    exact id (Eq.symm h)
  have zero_e := Eq.symm e_zero
  exact {
    n := 0,
    ι := λ i => 0,
    h := λ i => IsIdempotentElem.zero,
    sum_one := by
      have neki := Eq.symm (corner_ring_one idem_e)
      calc (0 : CornerSubring idem_e) = (⟨e, by exact e_in_corner_ring idem_e⟩ : CornerSubring idem_e) := by exact Subtype.ext_iff_val.2 zero_e
                                  _ = (1 : CornerSubring idem_e) := by exact rfl
    orthogonal := by simp only [IsEmpty.forall_iff, implies_true]
    div := by simp only [ZeroMemClass.coe_zero, IsEmpty.forall_iff]
  }


def idempotents {α : Type*} {n : ℕ} (x : α) (h : Fin n → α) : Fin (n + 1) → α :=
  Fin.cases x h

lemma idempotents_first {α : Type*} {n : ℕ} (x : α) (h : Fin n → α) : idempotents x h 0 = x := by
  exact rfl

lemma idempotents_rest {α : Type*} {n : ℕ} (x : α) (h : Fin n → α) (i : Fin n) : idempotents x h (Fin.succ i) = h i := by exact rfl

-- (Removed duplicate incomplete definition)

def extend_idempotents {n : ℕ} (f : R) (idem_f : IsIdempotentElem f) (es : Fin n → R) (h : (i : Fin n) → IsIdempotentElem (es i)) : (i : Fin (n+1)) → (IsIdempotentElem ((idempotents f es) i)) :=
  Fin.cases idem_f h

lemma bot_eq_span_zero (I : Ideal R) (e : R) (h_bot : I ≠ ⊥) (h_span : I = Ideal.span {e}) : e ≠ 0 := by -- Maša
  intro e_zero
  rw [← Ideal.span_singleton_eq_bot, ← h_span] at e_zero
  exact h_bot e_zero

def extension_of_ort_idem (e : R) (idem_e : IsIdempotentElem e) (oi : OrtIdem (CornerSubring (IsIdempotentElem.one_sub idem_e))) : OrtIdem R := {
  n := oi.n + 1,
  ι := idempotents e (fun (i : Fin oi.n) => oi.ι i),
  h := sorry--extend_idempotents e idem_e oi.ι oi.h,
  sum_one := by
    rw [Fin.sum_univ_succ]
    rw [idempotents_first]
    apply add_eq_of_eq_sub'
    #check oi.sum_one
    have one_sub_e_unit : 1 - e = (1 : CornerSubring (IsIdempotentElem.one_sub idem_e)) := by rfl
    simp [one_sub_e_unit]
    rw [← oi.sum_one]
    --calc _ = (∑ i : Fin (OrtIdem.n ↥(CornerSubring (IsIdempotentElem.one_sub idem_e))), OrtIdem.ι i) := by sorry
        --_ = ↑(∑ i : Fin (OrtIdem.n ↥(CornerSubring (IsIdempotentElem.one_sub idem_e))), OrtIdem.ι i) := by sorry
--rw [AddSubmonoidClass.coe_finset_sum (fun i => OrtIdem.ι i) (Finset.univ)]


    --rw [one_sub_e_unit]
    --rw [idempotents_rest]
    --rw [oi.sum_one]

    sorry
    --have h_sum := oi.sum_one
    --rw [← idempotents_first e oi.ι, ← idempotents_rest e oi.ι] at h_sum
    --exact h_sum,
  orthogonal := by
    intro i j
    by_cases (i = 0)




    sorry


    sorry
    --intro i j
    --have h_ort := oi.orthogonal i j
    --rw [← idempotents_first e oi.ι, ← idempotents_rest e oi.ι] at h_ort
    --exact h_ort
}

noncomputable
def subideals_nice_ideal_nice' [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (hi : ∀ J, J < I → NiceIdeal J) : NiceIdeal I := by
  by_cases h_zero : I = ⊥
  rw [h_zero]
  exact zero_ideal_nice

  intro h_idem_I e idem_e I_span_e

  have e_nonzero : e ≠ 0 := by exact bot_eq_span_zero I e h_zero I_span_e

  have corner_nontriv : Nontrivial (CornerSubring idem_e) := by exact corner_nontrivial R idem_e e_nonzero
  have corner_prime : IsPrimeRing (CornerSubring idem_e) := by exact corner_ring_prime idem_e h_prime
  have corner_artinian : IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by exact corner_ring_artinian idem_e

  obtain h := prime_and_artinian_esists_idem_corner_div corner_prime corner_artinian
  let f' := Classical.choose h
  have h_spec : f' ≠ 0 ∧ IsIdempotentElem f' ∧ IsDivisionSubring (CornerSubringNonUnital f') f' :=
    Classical.choose_spec h
  let fnz := h_spec.left
  let idem_f := h_spec.2.1
  let div_f := h_spec.2.2
  let f := f'.val
  let hf := f'.property

  have fnzR : f ≠ 0 := by exact (nonzero idem_e f').mp fnz
  have idem_one_sub_e : IsIdempotentElem (1 - e) := by exact IsIdempotentElem.one_sub idem_e
  have f_mem : f ∈ both_mul e e := by exact hf
  have idem_f_val : IsIdempotentElem f := by
    have pl := congrArg Subtype.val idem_f; simp only [NonUnitalSubring.val_mul] at pl; exact pl

  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f := by exact f_in_corner_othogonal (1- e) f idem_one_sub_e (by simp; exact hf)

  have idem_e_sub_f : IsIdempotentElem (e - f) := by exact f_mem_corner_e_e_sub_f_idem e f idem_e idem_f_val hf

  have e_sub_f_mem : (e - f) ∈ both_mul e e := by
    have e_mem : e ∈ both_mul e e := by use 1; simp; exact Eq.symm (CancelDenoms.derive_trans₂ rfl rfl idem_e)
    apply both_mul_sub
    exact e_mem
    exact f_mem

  let J : Ideal R := Ideal.span {e - f}

  have J_sub_I : J < I := by
    rw [I_span_e]
    apply e_span_larger_e_sub_f e f ⟨idem_one_sub_e, idem_f_val, one_sub_e_f_orthogonal⟩ fnzR

  have J_nice := hi J J_sub_I
  have J_idem : IdemIdeal J := by use e - f
  specialize J_nice J_idem (e - f) idem_e_sub_f rfl

  --let ⟨Joi, Jdiv⟩ := J_nice
  --let ⟨n, es, h_idem, h_sum, ⟨h_ort, h_div⟩⟩ := J_nice

  --exact {
  --  n := J_nice.n + 1,
  --  ι := idempotents ⟨f, hf⟩ ((coercion_to_eRe e (e - f) idem_e idem_e_sub_f e_sub_f_mem) ∘ --J_nice.ι)
  --  h := extend_idempotents (⟨f, hf⟩ : CornerSubring idem_e) idem_f ((coercion_to_eRe e (e - --f) idem_e idem_e_sub_f e_sub_f_mem) ∘ J_nice.ι) sorry,
  --  sum_one := by sorry
  --  orthogonal := by sorry
  --  div := by sorry
  --}
  sorry

noncomputable
def acc_ideal_nice [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (h_acc : Acc (fun x y => x < y) I) : NiceIdeal I := by
  induction h_acc with
  | intro J h_acc_J hJ =>
    exact subideals_nice_ideal_nice' h_prime h_art J hJ


theorem OrtIdem_HasMatrixUnits (R : Type*) [Ring R] (ort_idem : OrtIdem R) : ∃ (n : ℕ), HasMatrixUnits R n := by sorry


  --have hfRf : (both_mul (⟨f, hf⟩ : CornerSubring idem_e) ⟨f, hf⟩) = both_mul (f : R) (f : R) := by exact both_mul_lift idem_e ⟨f, hf⟩ ⟨f, hf⟩
