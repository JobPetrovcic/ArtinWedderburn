import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Init.Data.Fin.Basic
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import Mathlib.Algebra.Group.Basic
--import ArtinWedderburn.MatrixUnits
import ArtinWedderburn.Idempotents
import ArtinWedderburn.CornerCornerLemma

import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Ring.Defs

import Mathlib.RingTheory.SimpleModule

variable {R : Type*} [Ring R]
universe u

def IdemIdeal (I : Ideal R) : Prop := ∃ (e : R), IsIdempotentElem e ∧ I = Ideal.span {e}

lemma idem_lift_is_idem {e : R} {idem_e : IsIdempotentElem e} (f : CornerSubring idem_e) (hf : IsIdempotentElem f) : IsIdempotentElem (f : R) := by
  unfold IsIdempotentElem at *
  nth_rewrite 3 [←hf]
  rfl

--def OrtIdemDiv (R : Type u) [Ring R] : Prop := OrtIdem R  ∧ (∀ i, IsDivisionRing (CornerSubring (h i)))
--def NiceIdeal' (I : Ideal R) : Prop := IdemIdeal I → ∃ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} ∧ OrtIdem (CornerSubring idem)

def NiceIdeal (I : Ideal R) := IdemIdeal I → ∀ (e : R) (idem : IsIdempotentElem e), I = Ideal.span {e} → OrtIdemDiv (CornerSubring idem) -- Maša

def zero_ideal_nice : NiceIdeal (⊥ : Ideal R) := by -- Maša and Matevz
  intro IdemIdeal_zero e idem_e h
  have e_zero : e = 0 := by
    rw [← Ideal.span_singleton_eq_bot]
    exact id (Eq.symm h)
  have zero_e := Eq.symm e_zero
  exact {
    n := 0,
    f := λ i => 0,
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

lemma i_nonzero_succ {n : ℕ} (i : Fin (n + 1)) (i_nonzero : i ≠ 0): ∃(k : Fin n), i = k.succ := by
      refine Fin.eq_succ_of_ne_zero (by exact i_nonzero)


lemma bot_eq_span_zero (I : Ideal R) (e : R) (h_bot : I ≠ ⊥) (h_span : I = Ideal.span {e}) : e ≠ 0 := by -- Maša
  intro e_zero
  rw [← Ideal.span_singleton_eq_bot, ← h_span] at e_zero
  exact h_bot e_zero

def extension_of_ort_idem (e : R) (idem_e : IsIdempotentElem e) (oi : OrtIdem (CornerSubring (IsIdempotentElem.one_sub idem_e))) : OrtIdem R := {
  n := oi.n + 1,
  f := idempotents e (fun (i : Fin oi.n) => oi.f i),

  h := extend_idempotents e idem_e (fun (i : Fin oi.n) => oi.f i) (fun (i : Fin oi.n) => (by simp; apply e_idem_to_e_val_idem; exact oi.h i)),
  sum_one := by
    rw [Fin.sum_univ_succ]
    rw [idempotents_first]
    apply add_eq_of_eq_sub'
    have one_sub_e_unit : 1 - e = (1 : CornerSubring (IsIdempotentElem.one_sub idem_e)) := by rfl
    simp [one_sub_e_unit]
    rw [← oi.sum_one]
    calc
      ∑ i : Fin oi.n, idempotents e (fun i ↦ ↑(oi.f i)) i.succ = ∑ i : Fin oi.n, (fun i ↦ ↑(oi.f i)) i := by rfl
      _ = ↑(∑ i : Fin oi.n, oi.f i) := by exact Eq.symm (AddSubmonoidClass.coe_finset_sum oi.f Finset.univ)
  orthogonal := by
    intro i j i_neq_j
    have h1 : idempotents e (fun i ↦ ↑(oi.f i)) 0 = e := by exact rfl

    by_cases hi : i = 0

    rw [hi]
    let ⟨k, hk⟩ := i_nonzero_succ j (by exact Ne.symm (ne_of_eq_of_ne (id (Eq.symm hi)) i_neq_j))
    have h2 : idempotents e (fun i ↦ ↑(oi.f i)) j = oi.f k := by rw [hk]; exact rfl
    rw [h1, h2]
    apply f_in_corner_othogonal
    exact idem_e
    exact Subtype.coe_prop (oi.f k)

    let ⟨k, hk⟩ := i_nonzero_succ i (by exact hi)
    have h1' : (idempotents e (fun i ↦ ↑(oi.f i)) i) = oi.f k := by rw [hk]; exact rfl
    rw [h1']

    by_cases hj : j = 0
    rw [hj, h1]
    apply ort_comm
    apply f_in_corner_othogonal
    exact idem_e
    exact Subtype.coe_prop (oi.f k)

    let ⟨l,hl⟩ := i_nonzero_succ j (by exact hj)
    have h2' : (idempotents e (fun i ↦ ↑(oi.f i)) j) = oi.f l := by rw [hl]; exact rfl
    rw [h2']
    have k_neq_l : k ≠ l := by
      have k_neq_l' : k.succ ≠ l.succ := by rw [← hk, ← hl]; exact i_neq_j
      exact fun a ↦ k_neq_l' (congrArg Fin.succ a)
    let ort := oi.orthogonal k l k_neq_l
    apply orth_coercion
    exact ort
}
set_option pp.proofs true

def extension_of_OrtIdemDiv (e : R) (idem_e : IsIdempotentElem e) (div_e : IsDivisionRing (CornerSubring idem_e)) (oid : OrtIdemDiv (CornerSubring (IsIdempotentElem.one_sub idem_e))) : OrtIdemDiv R := {
  toOrtIdem := extension_of_ort_idem e idem_e oid.toOrtIdem,
  div := by

    have hn : (extension_of_ort_idem e idem_e oid.toOrtIdem).n = oid.n + 1 := by rfl
    intro i
    change Fin (oid.n + 1) at i
    by_cases hi : i = 0
    rw [hi]
    exact div_e

    have ⟨k, hk⟩ := i_nonzero_succ i (by exact hi)
    have h1 : oid.f k = (extension_of_ort_idem e idem_e oid.toOrtIdem).f i := by rw [hk]; rfl

    apply @isomorphic_rings_div_iff (CornerSubring (oid.h k)) _ (CornerSubring ((extension_of_ort_idem e idem_e oid.toOrtIdem).h i)) _
    symm
    have eq_el : (extension_of_ort_idem e idem_e oid.toOrtIdem).f i = oid.f k := by exact id (Eq.symm h1)
    have hc1 : CornerSubring ((extension_of_ort_idem e idem_e oid.toOrtIdem).h i) ≃+* (CornerSubring (e_idem_to_e_val_idem (oid.h k))):= (eq_el_iso_corner ((extension_of_ort_idem e idem_e oid.toOrtIdem).f i) (oid.f k) ((extension_of_ort_idem e idem_e oid.toOrtIdem).h i) (e_idem_to_e_val_idem (oid.h k)) eq_el)
    have hc2 : (CornerSubring (e_idem_to_e_val_idem (oid.h k))) ≃+* CornerSubring (oid.h k) := by
      symm
      apply @corner_ring_unital_eq R _


    exact RingEquiv.trans hc1 hc2
    --apply corner_ring_unital_eq
    --sorry
    exact oid.div k
    /-
    calc _ ≃+* CornerSubring (e_idem_to_e_val_idem (oid.h k)) := (eq_el_iso_corner ((extension_of_ort_idem e idem_e oid.toOrtIdem).f i) (oid.f k) ((extension_of_ort_idem e idem_e oid.toOrtIdem).h i) (e_idem_to_e_val_idem (oid.h k)) eq_el)
         _ ≃+* ↑(CornerSubring (oid.h k)) := by sorry

    --apply corner_ring_unital_eq
    sorry
    exact oid.div k
    -/
}
-- f(1 - e)R(1 - e)f = fRf  corner_ring_unital_eq
-- { x : ↥(CornerSubring (IsIdempotentElem.one_sub idem_e)) // x ∈ CornerSubring (oid.h k) } : Prop = { x : R // x ∈ CornerSubring ((extension_of_ort_idem e idem_e oid.toOrtIdem).h i) }

noncomputable
def subideals_nice_ideal_nice [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (hi : ∀ J, J < I → NiceIdeal J) : NiceIdeal I := by
  by_cases h_zero : I = ⊥
  rw [h_zero]
  exact zero_ideal_nice

  intro h_idem_I e idem_e I_span_e

  have e_nonzero : e ≠ 0 := by exact bot_eq_span_zero I e h_zero I_span_e

  have corner_nontriv : Nontrivial (CornerSubring idem_e) := by exact e_nonzero_corner_nontrivial R idem_e e_nonzero
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
  have idem_f_val : IsIdempotentElem f := by exact e_idem_to_e_val_idem idem_f

  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f := by exact f_in_corner_othogonal (1 - e) f idem_one_sub_e (by simp; exact hf)

  have idem_e_sub_f : IsIdempotentElem (e - f) := by exact f_mem_corner_e_e_sub_f_idem e idem_e ⟨f, f_mem⟩ idem_f

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

  have f_div : IsDivisionRing (CornerSubring idem_f) := by
    apply div_subring_to_div_ring
    exact div_f

  apply extension_of_OrtIdemDiv
  exact f_div
  #check IsIdempotentElem.one_sub idem_f
  #check idem_e_sub_f
  have h: (CornerSubring (IsIdempotentElem.one_sub idem_f)) ≃+* ↥(CornerSubring idem_e_sub_f) := by
    have eq_el : (1 : CornerSubring idem_e) - f' = ⟨e, by exact e_in_corner_ring idem_e⟩  - f' := by
      rw [@Subtype.ext_iff_val, @AddSubgroupClass.coe_sub, corner_ring_one]
      exact rfl
    --apply @corner_ring_unital_eq R _
    #check eq_el_iso_corner (1 - f') ⟨e - f, by sorry⟩ (IsIdempotentElem.one_sub idem_f) ()
    --have iso1 : (CornerSubring (IsIdempotentElem.one_sub idem_f)) ≃+*
    --apply eq_el_iso_corner (1 - f') (e - f) (IsIdempotentElem.one_sub idem_f) idem_e_sub_f
    sorry
  exact isomorphic_OrtIdemDiv (id h.symm) (hi J J_sub_I J_idem (e - f) idem_e_sub_f rfl)


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

noncomputable
def acc_ideal_nice [Nontrivial R] (h_prime : IsPrimeRing R) (h_art : IsArtinian R R) (I : Ideal R) (h_acc : Acc (fun x y => x < y) I) : NiceIdeal I := by
  induction h_acc with
  | intro J h_acc_J hJ =>
    exact subideals_nice_ideal_nice h_prime h_art J hJ


  --have hfRf : (both_mul (⟨f, hf⟩ : CornerSubring idem_e) ⟨f, hf⟩) = both_mul (f : R) (f : R) := by exact both_mul_lift idem_e ⟨f, hf⟩ ⟨f, hf⟩
