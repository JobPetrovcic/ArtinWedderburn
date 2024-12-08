import ArtinWedderburn.IdealProd
import ArtinWedderburn.SetProd
import Init.Classical

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


-- So all this is just to prove the first to lines of lemma 2.12 Bresar's paper

-- Lemma 2.12
-- hypothesis: I^2 ≠ ⊥ and I is a minimal left ideal
-- conclusion: there exists an idempotent e in I such that I = Re and eRe is a Division Ring (TODO) Dude this has to be divided into multiple lemmas
theorem minimal_ideal_I_sq_nonzero_exists_idem (h : IsAtom I) (I_sq_ne_bot : I * I ≠ ⊥) :
  ∃ e : R, IsIdempotentElem e ∧ e ∈ I ∧ I = Ideal.span {e} := by sorry -- Matevz
