import ArtinWedderburn.IdealProd
import ArtinWedderburn.SetProd
import Init.Classical
import ArtinWedderburn.CornerRing
import Mathlib.Order.Defs

variable {R : Type*} [Ring R]
variable (I J : Ideal R)

def sub_ideal_set (I : Ideal R) (a : R) : Set R := {r | ∃ x ∈ I, r = x * a}

-- Maybe a different name would be more appropriate as sub_ideal I a is not a necesarily contained in I
def sub_ideal (I : Ideal R) (a : R) : Ideal R := {  -- Done by Matevz
  carrier := sub_ideal_set I a,
  zero_mem' := by
    use 0
    constructor
    · exact Submodule.zero_mem I
    · simp,
  add_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
    use r + s
    constructor
    · exact I.add_mem hr hs
    · rw [hx, hy]
      noncomm_ring,
  smul_mem' := by
    rintro c x ⟨r, hr, hx⟩
    use c * r
    constructor
    · exact I.smul_mem c hr
    · rw [hx]
      noncomm_ring
}

theorem sub_ideal_le_ideal (I : Ideal R) (a : R) (h : a ∈ I) : sub_ideal I a ≤ I := by  -- Done by Matevz
  rintro x ⟨r, hr, ha⟩
  rw [ha]
  exact Ideal.mul_mem_left I r h

open Pointwise Set


theorem mul_ne_zero_imply_set_ne_zero (I J : Ideal R) (h : I * J ≠ ⊥) : ∃ x ∈ I, ∃ y ∈ J, x * y ≠ 0 := by -- Done by Matevz
  have hnzz : ∃ z, z ∈ (↑I : Set R) * (↑J : Set R) ∧ z ≠ 0 := not_subset.mp ((not_iff_not.mpr Ideal.span_eq_bot).mp h)
  obtain ⟨z, ⟨⟨x, ⟨hx, ⟨y, ⟨hy, hz⟩⟩⟩⟩, hnz⟩⟩ := hnzz
  use x
  constructor
  · exact hx
  · use y
    constructor
    · exact hy
    · simp at hz
      rw [hz]
      exact hnz


theorem ideal_sq_ne_bot_imply_subideal_ne_bot (I : Ideal R) (h : I * I ≠ ⊥) : ∃ y ∈ I, sub_ideal I y ≠ ⊥ := by -- Done by Matevz
  obtain ⟨x, hx, y, hy, hxy⟩ := mul_ne_zero_imply_set_ne_zero I I h
  use y
  constructor
  · exact hy
  · refine (Submodule.ne_bot_iff (sub_ideal I y)).mpr ?h.right.a
    use x * y
    constructor
    · use x
    · exact hxy

theorem ideal_sq_ne_bot_imply_subideal_ne_bot2 (I : Ideal R) (h : I * I ≠ ⊥) : ∃ y ∈ I, y ≠ 0 ∧ sub_ideal I y ≠ ⊥ := by -- Done by Matevz
  obtain ⟨x, hx, y, hy, hxy⟩ := mul_ne_zero_imply_set_ne_zero I I h
  use y
  constructor
  · exact hy
  · constructor
    · intro hc
      apply hxy
      rw [hc]
      simp
    · refine (Submodule.ne_bot_iff (sub_ideal I y)).mpr ?h.right.a
      use x * y
      constructor
      · use x
      · exact hxy

theorem le_and_not_lt_eq (I J : Ideal R) (h1 : I ≤ J) (h2 : ¬ (I < J)) : I = J := by -- Done by Matevz
  rw [lt_iff_le_and_ne] at h2
  push_neg at h2
  exact h2 h1


theorem minimal_ideal_I_sq_nonzero_exists_el (hI : IsAtom I) (hII : I * I ≠ ⊥) : ∃ y : R, y ∈ I ∧ sub_ideal I y = I := by -- Done by Matevz
  obtain ⟨y, ⟨hy, hyI⟩⟩ := ideal_sq_ne_bot_imply_subideal_ne_bot I hII
  use y
  constructor
  · exact hy
  · obtain ⟨Inz, hsi⟩ := hI
    have h1 := sub_ideal_le_ideal I y hy
    have h2 := fun b => hyI (hsi (sub_ideal I y) b)
    exact le_and_not_lt_eq (sub_ideal I y) I h1 h2

theorem minimal_ideal_I_sq_nonzero_exists_el2 (hI : IsAtom I) (hII : I * I ≠ ⊥) : ∃ y : R, y ∈ I ∧ y ≠ 0 ∧ sub_ideal I y = I := by -- Done by Matevz
  obtain ⟨y, ⟨hy, ynz, hyI⟩⟩ := ideal_sq_ne_bot_imply_subideal_ne_bot2 I hII
  use y
  constructor
  · exact hy
  · constructor
    · exact ynz
    · obtain ⟨Inz, hsi⟩ := hI
      have h1 := sub_ideal_le_ideal I y hy
      have h2 := fun b => hyI (hsi (sub_ideal I y) b)
      exact le_and_not_lt_eq (sub_ideal I y) I h1 h2

theorem minimal_ideal_I_sq_nonzero_exists_els2 (hI : IsAtom I) (hII : I * I ≠ ⊥) : ∃ y : R, y ∈ I ∧ y ≠ 0 ∧ sub_ideal I y = I ∧ ∃ e ∈ I, e ≠ 0 ∧ y = e * y := by -- Done by Matevz
  obtain ⟨y, ⟨hy, ynz, hI⟩⟩ := minimal_ideal_I_sq_nonzero_exists_el2 I hI hII
  use y
  constructor
  · exact hy
  · constructor
    · exact ynz
    · constructor
      · exact hI
      · rw [← hI] at hy
        obtain ⟨e, ⟨he, hey⟩⟩ := hy
        use e
        constructor
        · exact he
        · constructor
          · by_contra hez
            have yz : y = 0 := by calc
              y = e * y := hey
              _ = 0 * y := by rw [hez]
              _ = 0 := by noncomm_ring
            contradiction
          · exact hey




theorem minimal_ideal_I_sq_nonzero_exists_els (hI : IsAtom I) (hII : I * I ≠ ⊥) : ∃ y : R, y ∈ I ∧ sub_ideal I y = I ∧ ∃ e ∈ I, y = e * y := by -- Done by Job and Matevz
  obtain ⟨y, ⟨hy, hI⟩⟩ := minimal_ideal_I_sq_nonzero_exists_el I hI hII
  use y
  constructor
  · exact hy
  · constructor
    · exact hI
    · rw [← hI] at hy
      obtain ⟨e, ⟨he, hey⟩⟩ := hy
      use e


def elem_ann (I : Ideal R) (a : R) : Ideal R := { -- Done by Job and Matevz
  carrier := {x | x ∈ I ∧ x * a = 0},
  zero_mem' := by simp,
  add_mem' := by
    rintro x y hx hy
    constructor
    · exact Submodule.add_mem I hx.1 hy.1
    · rw [right_distrib, hx.2, hy.2, add_zero],
  smul_mem' := by
    rintro c x ⟨hx, hxa⟩
    constructor
    · exact Submodule.smul_mem I c hx
    · simp [mul_assoc, hxa]
}

theorem elem_ann_le_ideal (I : Ideal R) (a : R) : elem_ann I a ≤ I := by -- Done by Job and Matevz
  rintro x ⟨hx, hxa⟩
  exact hx

theorem e_semiidem (I : Ideal R) (e y : R) (he : e ∈ I) (h : e * y = y) : (e * e - e) ∈ (elem_ann I y) := by -- Done by Matevz
  unfold elem_ann
  simp
  constructor
  · have hde : e * e - e = (e - 1) * e := by noncomm_ring
    rw [hde]
    exact Ideal.mul_mem_left I (e - 1) he
  · calc
      (e * e - e) * y = e * (e * y - y) := by noncomm_ring
      _ = 0 := by rw [h]; simp


theorem strict_contain (I J : Ideal R) (hleq : I ≤ J) (hneq : ∃ x, x ∈ J ∧ x ∉ I) : I < J := by -- Done by Matevz
  constructor
  · exact hleq
  · rintro heq
    obtain ⟨x, hxJ, hxnI⟩ := hneq
    apply heq at hxJ
    contradiction

theorem ideal_neq_bot_if_has_nonzero_el (I : Ideal R) (h : ∃ x ∈ I, x ≠ 0) : I ≠ ⊥ := by -- Done by Matevz
  by_contra hI
  obtain ⟨x, hx, xnz⟩ := h
  rw [hI] at hx
  contradiction



theorem nonzero_ideal_in_min_ideal (I J : Ideal R) (atom_I : IsAtom I) (Jnz : J ≠ ⊥) (hJsubI : J ≤ I) : J = I := by -- Done by Matevz
  by_contra hcon
  have hJltI : J < I := lt_of_le_of_ne hJsubI hcon
  have span_eq_bot : J = ⊥ := atom_I.right J hJltI
  contradiction

theorem minimal_ideal_I_sq_nonzero_exists_idem (h_atom_I : IsAtom I) (hII : I * I ≠ ⊥) : -- Done by Matevz
  ∃ e : R, e ∈ I ∧ e ≠ 0 ∧ IsIdempotentElem e ∧ Ideal.span {e} = I := by
  obtain ⟨y, ⟨hy, ynz, hyI, ⟨e, he, henz, hey⟩⟩⟩ := minimal_ideal_I_sq_nonzero_exists_els2 I h_atom_I hII
  obtain hye : e * y = y := by exact id (Eq.symm hey)
  obtain h12 := e_semiidem I e y he hye
  have hneq : ∃ x, x ∈ I ∧ x ∉ elem_ann I y := by
    use e
    constructor
    · exact he
    · unfold elem_ann
      simp
      rw [hye]
      tauto
  have h_ann_sub : elem_ann I y < I := strict_contain (elem_ann I y) I (elem_ann_le_ideal I y) hneq
  have ann_zero : elem_ann I y = ⊥ := h_atom_I.2 (elem_ann I y) h_ann_sub
  use e
  constructor
  · exact he
  · constructor
    · exact henz
    · constructor
      · unfold IsIdempotentElem
        rw [ann_zero] at h12
        calc
        e * e = (e * e - e) + e := by noncomm_ring
            _ = 0 + e := by rw [h12]
            _ = e := by abel
      · have span_neq_bot : Ideal.span {e} ≠ ⊥ := by
          by_contra hRe
          have einspane : e ∈ Ideal.span {e} := Ideal.mem_span_singleton_self e
          rw [hRe] at einspane
          contradiction
        by_contra hcon
        have hspanltI : (Ideal.span {e} : Ideal R) < I := lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr he) hcon
        have span_eq_bot : Ideal.span {e} = ⊥ := h_atom_I.right (Ideal.span {e}) hspanltI
        contradiction








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

theorem div_subring_to_div_ring (e : R) (idem_e : IsIdempotentElem e) (h : IsDivisionSubring (CornerSubringNonUnital e) e) : IsDivisionRing (CornerSubring idem_e) := by --Maša
  obtain ⟨⟨a, ⟨a_mem, a_nz⟩⟩, h_inv⟩ := h
  have corner_nontrivial : Nontrivial (CornerSubring idem_e) := by
    use (⟨a, a_mem⟩ : CornerSubring idem_e), ⟨0, by exact NonUnitalSubring.zero_mem (CornerSubring idem_e)⟩
    simp_all
  apply left_inv_implies_divring
  clear a a_mem a_nz
  intro x x_nz
  let ⟨y, ⟨y_mem, hy⟩⟩ := h_inv x (by exact SetLike.coe_mem x) (by exact (nonzero idem_e x).mp x_nz)
  use ⟨y, y_mem⟩
  rw [Subtype.ext_iff_val]
  simp
  exact hy

-- Lemma 2.12
-- hypothesis: I^2 ≠ ⊥ and I is a minimal left ideal
-- conclusion: there exists an idempotent e in I such that I = Re and eRe is a Division Ring (TODO) Dude this has to be divided into multiple lemmas

theorem corner_ring_div (h_atom_I : IsAtom I) (e : R) (e_in_I : e ∈ I) (henz : e ≠ 0) (he_idem : IsIdempotentElem e) : IsDivisionSubring (CornerSubringNonUnital e) e := by -- Done by Matevz
  constructor
  · use e
    constructor
    · use e
      rw [he_idem, he_idem]
    · exact henz
  · intro x hx
    unfold CornerSubringNonUnital at hx
    obtain ⟨r, _, _⟩ := hx
    intro erenz
    have hsubI : left_ideal_of_element (e * r * e) ≤ I := by
      rintro x ⟨y, hy⟩
      have hx : x = (y * e * r) * e := by calc
        x = y * (e * r * e) := hy
        _ = (y * e * r) * e := by noncomm_ring
      rw [hx]
      exact Ideal.mul_mem_left I (y * e * r) e_in_I
    have hnz : left_ideal_of_element (e * r * e) ≠ ⊥ := by
      refine ideal_neq_bot_if_has_nonzero_el (left_ideal_of_element (e * r * e)) ?k
      use e * r * e
      constructor
      · use 1
        simp
      · exact erenz
    have heq : left_ideal_of_element (e * r * e) = I := nonzero_ideal_in_min_ideal I (left_ideal_of_element (e * r * e)) h_atom_I hnz hsubI
    obtain ⟨s, hs⟩ := (Ideal.ext_iff.mp heq e).mpr e_in_I
    use e * s * e
    constructor
    · use s
    · calc (e * s * e) * (e * r * e) = e * s * (e * e) * r * e := by noncomm_ring
        _ = e * (s * (e * r * e)) := by rw [he_idem]; noncomm_ring
        _ = e := by rw [←hs,he_idem]



-- The lemma of this file
theorem minimal_ideal_I_sq_nonzero_exists_idem_and_div (h_atom_I : IsAtom I) (hII : I * I ≠ ⊥) : -- Done by Matevz
  ∃ e : R, e ∈ I ∧ e ≠ 0 ∧ IsIdempotentElem e ∧ Ideal.span {e} = I ∧ IsDivisionSubring (CornerSubringNonUnital e) e := by
  obtain ⟨e, ⟨he, henz, he_idem, hspan, hdiv⟩⟩ := minimal_ideal_I_sq_nonzero_exists_idem I h_atom_I hII
  use e
  constructor
  · exact he
  · constructor
    · exact henz
    · constructor
      · exact he_idem
      · constructor
        · trivial
        · exact corner_ring_div (Ideal.span {e}) h_atom_I e he henz he_idem
