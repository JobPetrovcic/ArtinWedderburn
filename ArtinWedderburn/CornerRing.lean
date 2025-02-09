import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.NonUnitalToUnital

import ArtinWedderburn.Auxiliary

variable {R : Type*} [Ring R]
variable {e : R}

def CornerRingSet (e : R) : Set R := both_mul e e

-- an element x of R is in the corner ring if and only if x = e * x * e
theorem corner_ring_set_mem {x : R} (idem_e : IsIdempotentElem e): x ∈ CornerRingSet e ↔ x = e * x * e := by -- Done by Job
  constructor
  {rintro ⟨x, rfl⟩; rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, idem_e]; rw [← mul_assoc e x e, ← mul_assoc e (e *x) e, ← mul_assoc e e x, idem_e]}
  {intro hx; use x;}

theorem x_in_corner_x_eq_e_y_e {x : R} (h : x ∈ CornerRingSet e): ∃ (y : R), x = e * y * e := by exact h



-- I would much rather work with this, because this is the definition I used in Lemma 2.12
instance CornerSubringNonUnital (e : R) : NonUnitalSubring R where -- Done by Matevz
  carrier := both_mul e e
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r + s
    rw [hr, hs]
    noncomm_ring
  neg_mem' := by
    rintro x ⟨r, hr⟩
    use -r
    rw [hr]
    noncomm_ring
  mul_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r * e * e * s
    rw [hr, hs]
    noncomm_ring

theorem corner_ring_carrier : (CornerSubringNonUnital e).carrier = both_mul e e  := by rfl
theorem el_in_corner_ring (x : R) : x ∈ both_mul e e ↔  x ∈ CornerSubringNonUnital e := by rfl

theorem eq_carrier_eq_corner (x y : R) (h : both_mul x x = both_mul y y) : CornerSubringNonUnital x = CornerSubringNonUnital y := by
  apply NonUnitalSubring.ext
  simp only [← el_in_corner_ring, h, implies_true]


def CornerSubring (idem_e : IsIdempotentElem e) := CornerSubringNonUnital e

theorem CornerSubringEq (idem_e idem_e' : IsIdempotentElem e) : CornerSubring idem_e = CornerSubring idem_e' := by exact rfl
variable (idem_e : IsIdempotentElem e)

variable {x : R}

theorem subring_mem_idem : x ∈ CornerSubring idem_e ↔ x = e * x * e := by
  rw [← corner_ring_set_mem]; rfl; exact idem_e

-- if x and y are in the corner ring, then so is x * w * y
-- note that e does not have to be an idempotent element
theorem corner_ring_both_mul_mem (x w y : R) (hx : x ∈ CornerSubringNonUnital e) (hy : y ∈ CornerSubringNonUnital e): (x * w * y) ∈ CornerSubringNonUnital e := by -- Done by Job
  have ⟨u, hx⟩ := hx
  have ⟨v, hy⟩ := hy
  use u * e * w * e * v
  rw [hx, hy]
  noncomm_ring


-- if e is an idempotent element the it is the identity of the corner ring
theorem left_unit_mul (idem_e : IsIdempotentElem e) (h : x ∈ CornerSubringNonUnital e): e * x = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [←mul_assoc, ←mul_assoc, idem_e]

theorem right_unit_mul (idem_e : IsIdempotentElem e) (h : x ∈ CornerSubringNonUnital e): x * e = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [mul_assoc, mul_assoc, idem_e, mul_assoc]

open NonUnitalSubringClass

abbrev CornerSubringIsNonUNitalRing := toNonUnitalRing (CornerSubringNonUnital e)

theorem corner_ring_hom (a b : CornerSubringNonUnital e) : (a * b : CornerSubringNonUnital e) = (a : R) * (b : R) := by rfl

instance CornerRingOne (idem_e : IsIdempotentElem e): One (CornerSubring idem_e) := ⟨e, by rw [subring_mem_idem idem_e]; rw [idem_e, idem_e]⟩

--⟨⟨e, by rw [subring_mem_idem]; rw [idem_e, idem_e]⟩⟩

theorem corner_ring_one (idem_e : IsIdempotentElem e) : (1 : CornerSubring idem_e) = e := by rfl


theorem is_left_unit : ∀ (x : CornerSubring idem_e), 1 * x = x := by -- Done by Job
  rw [Subtype.forall]
  intro a hx
  apply Subtype.eq
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, left_unit_mul idem_e hx]
theorem is_right_unit : ∀ (x : CornerSubring idem_e), x * 1 = x := by -- Done by Job
  rw [Subtype.forall]
  intro a hx
  apply Subtype.eq
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, right_unit_mul idem_e hx]


lemma e_in_corner_ring : --Maša
  e ∈ (CornerSubring idem_e) := by
  rw [subring_mem_idem]
  rw [IsIdempotentElem.eq idem_e, IsIdempotentElem.eq idem_e]

theorem both_mul_one_one_eq_R : both_mul (1 : R) 1 = ⊤ := by
  ext x
  constructor
  · intro ⟨y, hy⟩
    trivial
  · intro hx
    use x
    noncomm_ring

def top_subring_equiv_ring (S : NonUnitalSubring R) (h : S.carrier = ⊤) : S ≃+* R := {
  toFun := fun a => a,
  invFun := fun a => ⟨a, by
    have ha : a ∈ S.carrier := by rw [h]; exact trivial
    exact ha
    ⟩,
  left_inv := by intro a; simp
  right_inv := by intro a; simp
  map_mul' := by intro a b; simp
  map_add' := by intro a b; simp
}

def iso_corner_one : CornerSubring ((IsIdempotentElem.one : IsIdempotentElem (1 : R))) ≃+* R := by
  apply top_subring_equiv_ring
  unfold CornerSubring
  rw [corner_ring_carrier]
  exact both_mul_one_one_eq_R



lemma nonzero (x : CornerSubring idem_e): (x : CornerSubring idem_e) ≠ 0 ↔ x.val ≠ 0 := by --Maša
  constructor
  · intro hnz hz
    apply hnz
    exact Subtype.ext hz
  · intro hnz hz
    rw [Subtype.ext_iff_val] at hz
    exact hnz hz


lemma e_nonzero_corner_nontrivial (R : Type*) [Ring R] {e : R} (idem_e : IsIdempotentElem e) (e_nonzero : e ≠ 0) : Nontrivial (CornerSubring idem_e) := by --Maša
  constructor
  use ⟨e, by exact e_in_corner_ring idem_e⟩
  use 0
  exact (nonzero idem_e ⟨e, e_in_corner_ring idem_e⟩).mpr e_nonzero


lemma eq_iff_val (x y z : CornerSubring idem_e) : (x + y).val = z.val ↔ x.val + y.val = z.val := by --Maša
  exact Eq.congr_right rfl

lemma e_x_e_in_corner : ∀ (x : R), e * x * e ∈ CornerSubring idem_e := by --Maša
  intro x
  rw [subring_mem_idem, eq_comm]
  calc _ = (e * e) * x * (e * e) := by noncomm_ring
        _ = e * x * e := by rw [idem_e]

-- The corner ring is a ring
instance CornerRingIsRing (idem_e : IsIdempotentElem e) : Ring (CornerSubring idem_e) := non_unital_w_e_is_ring 1 (is_left_unit idem_e) (is_right_unit idem_e) -- Done by Job

def coercion_to_eRe (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (f_mem : f ∈ CornerSubring idem_e) (x : CornerSubring idem_f): CornerSubring idem_e := by -- Maša and Job
  use x.val
  have h : x.val ∈ both_mul e e := by
    let ⟨y, hy⟩ := f_mem
    let ⟨z, hz⟩ := x.property
    rw [hz, hy]
    use (y * e * z * e * y)
    noncomm_ring
  exact h

-- If eRe is a division ring then e is nonzero
lemma corner_ring_division_e_nonzero --Maša
  (idem_e : IsIdempotentElem e) (heRe : IsDivisionRing (CornerSubring idem_e)) : e ≠ 0 := by
  by_contra he
  have ha : ∀(a : R), e * a * e = 0 := by exact fun a ↦ mul_eq_zero_of_right (e * a) he
  have h_zero : ∀(x : CornerSubring idem_e), x = 0 := by
    intro ⟨x, hx⟩
    apply x_in_corner_x_eq_e_y_e at hx
    obtain ⟨y, hy⟩ := hx
    specialize ha y
    rw [ha] at hy
    exact (NonUnitalSubring.coe_eq_zero_iff (CornerSubring idem_e)).mp hy
  obtain ⟨⟨x, hx⟩, _⟩ := heRe
  exact hx (h_zero x)



def equal_el_iso_matrix_rings' (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (e_eq_f : e = f) (n : ℕ) : Matrix (Fin n) (Fin n) (CornerSubring idem_e) ≃+* Matrix (Fin n) (Fin n) (CornerSubring idem_f) := by  --Maša
  let ψ : (CornerSubring idem_e) ≃+* (CornerSubring idem_f) := {
      toFun := fun x => ⟨x.val, by
        let ⟨y, hy⟩ := x.property
        have h : x = (f : R) * y * f := by rw [← e_eq_f]; exact hy
        use y⟩,
      invFun := fun x => ⟨x.val, by
        let ⟨y, hy⟩ := x.property
        have h : x = (e : R) * y * e := by rw [e_eq_f]; exact hy
        use y⟩,
      left_inv := fun x => rfl,
      right_inv := fun x => rfl,
      map_mul' := fun x y => rfl,
      map_add' := fun x y => rfl,
  }
  exact RingEquiv.mapMatrix ψ


def equal_el_iso_matrix_rings (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (e_eq_f : e = f) (n : ℕ) : Matrix (Fin n) (Fin n) (CornerSubringNonUnital e) ≃+* Matrix (Fin n) (Fin n) (CornerSubringNonUnital f) := by --Maša and Job
  let ψ : (CornerSubringNonUnital e) ≃+* (CornerSubringNonUnital f) := by rw [e_eq_f]
  apply equal_el_iso_matrix_rings'
  exact idem_e
  exact idem_f
  exact e_eq_f

--mapMatrix

--TODO: ↥(CornerSubring idem_e_sub_f) = (CornerSubring (IsIdempotentElem.one_sub idem_f)) in eRe

--lemma corner_eq (e : R) (idem_e : IsIdempotentElem e) (f : CornerSubring idem_e) (idem_f : IsIdempotentElem f) : CornerSubring (idem_f) = CornerSubring (idem_f) := by sorry

/-
theorem corner_equal (e : R) (idem_e : IsIdempotentElem e) (f : CornerSubring idem_e) (idem_f : IsIdempotentElem f): CornerSubring (f_mem_corner_e_e_sub_f_idem e idem_e f idem_f) = CornerSubring (IsIdempotentElem.one_sub idem_f) := by

  sorry
-/


-- coercions from Sets of CornerSubrings to Set of R
instance : CoeOut (Set (CornerSubring idem_e)) (Set R) := {coe := fun X => Set.image Subtype.val X}


-- I left ideal in eRe -> RI is a left ideal in R
def ideal_lift (I : Ideal (CornerSubring idem_e)) : Ideal R := Ideal.span (I.carrier) -- Maša


-- coercion from Ideals of CornerSubrings to Ideals of R
instance : CoeOut (Ideal (CornerSubring idem_e)) (Ideal R) := {coe := ideal_lift idem_e} -- Maša

-- I ⊆ J -> RI ⊆ RJ
theorem lift_monotonicity (I J : Ideal (CornerSubring idem_e)) : I ≤ J → (ideal_lift idem_e I) ≤ (ideal_lift idem_e J) := by -- Maša
  intro I_leq_J
  apply Ideal.span_mono
  exact Set.image_mono I_leq_J

def el_push (x : R) : CornerSubring idem_e := ⟨e * x * e, e_x_e_in_corner idem_e x⟩

def ideal_push (idem_e : IsIdempotentElem e) (J : Ideal R) : Ideal (CornerSubring idem_e) where -- Maša
  carrier := {el_push idem_e x | x ∈ J}
  zero_mem' := by
    use 0
    constructor
    · exact Submodule.zero_mem J
    · simp only [el_push]
      noncomm_ring
      rfl
  add_mem' := by
    rintro x y ⟨r, ⟨hr_mem, hr⟩⟩ ⟨s, ⟨hs_mem, hs⟩⟩
    use r + s
    constructor
    · exact (Submodule.add_mem_iff_right J hr_mem).mpr hs_mem
    · simp only [el_push] at *
      rw [←hr, ←hs]
      noncomm_ring
      rfl
  smul_mem' := by
    rintro ⟨c, ⟨a, hc⟩⟩ x ⟨r, ⟨hr_mem, hr⟩⟩
    use a * e  * e * r
    constructor
    · exact Ideal.mul_mem_left J (a * e *e) hr_mem
    · simp only [el_push, hc] at *
      rw [←hr]
      simp only [smul_eq_mul, MulMemClass.mk_mul_mk, Subtype.mk.injEq]
      noncomm_ring

theorem add_el_push_eq_add (x y : R) : el_push idem_e x + el_push idem_e y = el_push idem_e (x + y) := by
  simp only [el_push]
  noncomm_ring
  simp only [AddMemClass.mk_add_mk]

lemma el_push_smul_in_I (a y : R) (I : Ideal (CornerSubring idem_e)) : y ∈ (I.carrier : Set R) → el_push idem_e (a • y) ∈ I := by -- by Maša
  intro hy
  obtain ⟨r, ⟨hr1, hr2⟩⟩ := hy
  obtain ⟨s, hs⟩ := r.2
  rw [← hr2]
  have h : e * (a • r) * e = (e * a * e) * r := by
    calc _ = e * a * r * e := by noncomm_ring
         _ = e * a * (e * s * e) * e := by rw [hs]
         _ = e * a *  e * s * (e  * e) := by noncomm_ring
         _ = e * a * (e * e) * s * e := by rw [idem_e, ← idem_e]
         _ = e * a * e * (e * s * e) := by noncomm_ring
         _ = (e * a * e) * r := by rw [← hs]
  let w : CornerSubring idem_e := ⟨e * a * e, e_x_e_in_corner idem_e a⟩
  have h' : w * r ∈ I := by
    have hr : r ∈ I := by exact hr1
    exact Ideal.mul_mem_left I w hr
  let v : CornerSubring idem_e := el_push idem_e (a • r)
  have v_val : v.val = e * (a * r) * e := by
    unfold el_push at v
    exact rfl
  have h'' : v = w * r := by
    rw [Subtype.ext_iff_val]
    rw [@NonUnitalSubring.val_mul]
    simp only [v, w, el_push]
    exact h
  rw [← h''] at h'
  exact h'


theorem ideal_push_pull_inclusion (I : Ideal (CornerSubring idem_e)) (x : R) : (x ∈ ideal_lift idem_e I) → (el_push idem_e x) ∈ I := by --by Job and Maša
  intro hx
  induction hx using Submodule.closure_induction with
  | zero => simp [el_push]; exact (Submodule.Quotient.mk_eq_zero I).mp rfl
  | add y z hy hz hyp hyz => rw [←add_el_push_eq_add]; exact (Submodule.add_mem_iff_right I hyp).mpr hyz
  | smul_mem a y hy => exact el_push_smul_in_I idem_e a y I hy

#check Submodule.span_induction
theorem push_pull (idem_e : IsIdempotentElem e) (I : Ideal (CornerSubring idem_e)) : ideal_push idem_e (ideal_lift idem_e I) = I := by -- Maša
  ext x
  constructor
  · rintro ⟨y, ⟨hy_mem, hy⟩⟩
    rw [←hy]
    exact ideal_push_pull_inclusion idem_e I y hy_mem
  · intro hx
    have h : ↑x ∈ ideal_lift idem_e I := by
      unfold ideal_lift
      have hx1 : ↑x ∈ (I.carrier : Set R) := by exact Set.mem_image_of_mem Subtype.val hx
      exact (Ideal.mem_span ↑x).mpr fun p a ↦ a hx1
    unfold ideal_push
    use ↑x
    constructor
    · exact h
    · obtain ⟨y, hy⟩ := x.2
      have hx : ↑x ∈ CornerRingSet e := by exact Subtype.coe_prop x
      apply (corner_ring_set_mem idem_e).1 at hx
      unfold el_push
      symm
      exact SetLike.coe_eq_coe.mp hx

-- I have put this below push_pull, because it can be proven using push_pull and lift_monotonicity
theorem lift_strict_monotonicity (I J : Ideal (CornerSubring idem_e)) : I < J → (ideal_lift idem_e I) < (ideal_lift idem_e J) := by -- Maša
  intro I_leq_J
  have I_neq_J : I ≠ J := by exact ne_of_lt I_leq_J
  have lift_leq : (ideal_lift idem_e I) ≤ (ideal_lift idem_e J) := by
    exact lift_monotonicity idem_e I J (le_of_lt I_leq_J)
  have lift_neq : (ideal_lift idem_e I) ≠ (ideal_lift idem_e J) := by
    by_contra h_eq
    have h_eq : ideal_push idem_e (ideal_lift idem_e I) = ideal_push idem_e (ideal_lift idem_e J) := by
      exact congrArg (ideal_push idem_e) h_eq
    rw [push_pull, push_pull] at h_eq
    exact I_neq_J h_eq
  exact lt_of_le_of_ne lift_leq lift_neq



theorem lift_acc_then_ideal_acc (idem_e : IsIdempotentElem e) (J : Ideal R) (h_J_is_lift : ∃ I3 : Ideal (CornerSubring idem_e), J = ideal_lift idem_e I3) (h_acc_J : Acc (fun x y => x < y) J) : Acc (fun x y => x < y) (ideal_push idem_e J) := by -- done by Matevz
  induction h_acc_J with
  | intro J2 h_acc_j2 hi =>
    obtain ⟨I, hI⟩ := h_J_is_lift
    rw [hI, push_pull idem_e I]
    have c1 : (I2 : Ideal (CornerSubring idem_e)) → I2 < I → Acc (fun x y => x < y) I2 := by
      intro I2 hI2
      rw [←push_pull idem_e I2]
      have subJ2 := (lift_strict_monotonicity idem_e I2 I) hI2
      rw [←hI] at subJ2
      exact hi (ideal_lift idem_e I2) subJ2 (by use I2)
    exact Acc.intro I c1



-- Lemma 2.10
-- a) If R is artinian, then the corner ring is artinian
theorem corner_ring_artinian [h_ar : IsArtinian R R] : IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by -- done by Matevz
  unfold IsArtinian at *
  unfold WellFoundedLT at *
  have Iacc : ∀ I : Ideal R, Acc (fun x y => x < y) I := by
    intro I
    exact WellFounded.apply h_ar.wf I
  apply IsWellFounded.mk
  have allacc : ∀ I : Ideal (CornerSubring idem_e), Acc (fun x y => x < y) I := by
    intro I
    have h : Acc (fun x y => x < y) (ideal_push idem_e (ideal_lift idem_e I)) := lift_acc_then_ideal_acc idem_e I (by use I) (Iacc (ideal_lift idem_e I))
    rw [push_pull idem_e I] at h
    exact h
  exact WellFounded.intro allacc


theorem corner_ring_both_mul_mem' (x y : CornerSubring idem_e) (w : R) : x * w * y ∈ CornerSubring idem_e := by
  apply corner_ring_both_mul_mem
  exact x.property
  exact y.property

-- if a and b in eRe, then a (e R e) b = a R b as sets
theorem both_mul_lift (x y : CornerSubring idem_e) : (both_mul (x : CornerSubring idem_e)  y) = both_mul (x : R) (y : R) := by
  ext a
  constructor
  {
    rintro ⟨r, ⟨s, hs⟩, rfl⟩
    use s
    simp only [NonUnitalSubring.val_mul, hs]
  }
  {
    rintro ⟨s, hs⟩
    rw [←is_right_unit idem_e ↑x, ←is_left_unit idem_e ↑y] at hs
    simp only [NonUnitalSubring.val_mul] at hs
    let sc : R := (1 :(CornerSubring idem_e)) * s * (1 :(CornerSubring idem_e))
    rw [←mul_assoc] at hs
    have ha : a = x * sc * y := by
      simp only [sc]
      rw [hs]
      simp only [mul_assoc]
    have hsc : sc ∈ CornerSubring idem_e := by
      simp only [sc]
      apply corner_ring_both_mul_mem'
    use x * ⟨sc, hsc⟩ *y
    constructor
    {use ⟨sc, hsc⟩}
    {simp only [NonUnitalSubring.val_mul, ha]}
  }

-- b) If R is a prime ring, then the corner ring is prime
theorem corner_ring_prime (hRP : IsPrimeRing R) : IsPrimeRing (CornerSubring idem_e) := by  -- Job
  rw [prime_ring_equiv]
  intro a b h
  have h_lift : ((both_mul a b) : Set R) = {0} := by
    rw [←both_mul_lift, congrArg (Set.image Subtype.val) h]
    simp
  have l := prime_ring_equiv.1 hRP _ _ h_lift
  simp at l
  exact l


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
