import ArtinWedderburn.IdealProd
import ArtinWedderburn.SetProd
import Init.Classical
import ArtinWedderburn.CornerRing

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

theorem minimal_ideal_I_sq_nonzero_exists_el2 (hI : IsAtom I) (hII : I * I ≠ ⊥) : ∃ y : R, y ∈ I ∧ sub_ideal I y = I := by -- Done by Matevz
  obtain ⟨y, ⟨hy, _, hyI⟩⟩ := ideal_sq_ne_bot_imply_subideal_ne_bot2 I hII
  use y
  constructor
  · exact hy
  · obtain ⟨Inz, hsi⟩ := hI
    have h1 := sub_ideal_le_ideal I y hy
    have h2 := fun b => hyI (hsi (sub_ideal I y) b)
    exact le_and_not_lt_eq (sub_ideal I y) I h1 h2

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

theorem e_in_elem_ann (I : Ideal R) (e y : I) (h : (e : R) * y = y) : ((e : R) * e - e) ∈ (elem_ann I y) := by -- Done by Job (apply? part) and Matevz
  unfold elem_ann
  simp
  constructor
  · refine (Submodule.sub_mem_iff_left I ?left.hy).mpr ?left.a
    exact Submodule.coe_mem e
    refine Ideal.mul_mem_left I ↑e ?left.a.a
    exact Submodule.coe_mem e
  · suffices h13 : ((e : R) * e - e) * y = 0 by exact h13
    calc
      ((e : R) * e - e) * y = e * (e * y - y) := by noncomm_ring
      _ = 0 := by rw [h]; simp


theorem subideal_zero : sub_ideal I 0 = ⊥ := by
  ext x
  simp [sub_ideal, sub_ideal_set]
  intro hx
  use x
  exact (Submodule.Quotient.mk_eq_zero I).mp (congrArg Submodule.Quotient.mk hx)

theorem atom_neq_bot : IsAtom I → I ≠ ⊥ := by
  intro hI
  obtain ⟨Inz, hsi⟩ := hI
  intro hc
  apply Inz
  rw [hc]


theorem minimal_ideal_I_sq_nonzero_exists_idem (h_atom_I : IsAtom I) (hII : I * I ≠ ⊥) :
  ∃ e : I, IsIdempotentElem (e : R) ∧ I = Ideal.span {(e : R)} := by
  have ⟨Inz, hsi⟩ := h_atom_I
  obtain ⟨y, ⟨hy, hyI, ⟨e, he, hey⟩⟩⟩ := minimal_ideal_I_sq_nonzero_exists_els I h_atom_I hII
  --obtain ⟨h1, h2⟩ := some_lemma I ⟨e, he⟩ ⟨y, hy⟩ _
  have h1 : elem_ann I y ≤ I := elem_ann_le_ideal I y
  have hIyn0 : sub_ideal I y ≠ ⊥ := by exact Ne.symm (ne_of_ne_of_eq (id (Ne.symm Inz)) (id (Eq.symm hyI)))
  have h_ann_not_all : elem_ann I y ≠ I := by
    intro hc; apply hIyn0;
    refine (Submodule.eq_bot_iff (sub_ideal I y)).mpr ?_
    intro x hx
    simp [sub_ideal, sub_ideal_set] at hx
    obtain ⟨z, ⟨hzI, rfl⟩⟩ := hx
    have zann : z ∈ elem_ann I y := by rw [hc]; exact hzI
    exact zann.2
  have h_ann_zero : elem_ann I y = ⊥ := by
    apply hsi
    refine gt_iff_lt.mpr ?intro.a.a

    exact lt_of_le_of_ne h1 h_ann_not_all
  have k : (e : R) * e - e ∈ elem_ann I y := by apply e_in_elem_ann I ⟨e, he⟩ ⟨y, hy⟩ (by symm; exact hey)
  have k'' : ((e : R) * e - e) ∈ (⊥ : Ideal R) := by rw [← h_ann_zero]; exact k
  have is_idem : IsIdempotentElem (e : R) := by
    unfold IsIdempotentElem
    rw [← sub_eq_zero]
    exact k''
  use ⟨e, he⟩
  simp [is_idem]
  have hne : e ≠ 0 := by
    intro hc
    rw [hc] at hey
    simp only [zero_mul] at hey
    apply Inz
    rw [←hyI, hey]
    exact subideal_zero I
  have hIne : Ideal.span {e} ≠ 0 := by intro hc;apply hne; exact Submodule.span_singleton_eq_bot.mp hc
  have hIeunderI : Ideal.span {e} ≤ I := by exact (Ideal.span_singleton_le_iff_mem I).mpr he
  exact Eq.symm (le_and_not_lt_eq (Ideal.span {e}) I hIeunderI fun a ↦ hIne (hsi (Ideal.span {e}) a))




-- So all this is just to prove the first to lines of lemma 2.12 Bresar's paper

-- Lemma 2.12
-- hypothesis: I^2 ≠ ⊥ and I is a minimal left ideal
-- conclusion: there exists an idempotent e in I such that I = Re and eRe is a Division Ring (TODO) Dude this has to be divided into multiple lemmas
theorem minimal_ideal_I_sq_nonzero_exists_idem_and_div (h : IsAtom I) (I_sq_ne_bot : I * I ≠ ⊥) :
  ∃ e : R, IsIdempotentElem e ∧ e ∈ I ∧ I = Ideal.span {e} ∧ ∀ x : R, x ≠ 0 → ∃ y : R, x * y = 1 := by
  obtain ⟨y, ⟨hy, hI⟩⟩ := minimal_ideal_I_sq_nonzero_exists_el I h I_sq_ne_bot
  sorry
