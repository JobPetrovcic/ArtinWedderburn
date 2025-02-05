import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.NonUnitalToUnital
import Mathlib.Algebra.Ring.MinimalAxioms
import ArtinWedderburn.PrimeRing
import Mathlib.RingTheory.Ideal.Span

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


def CornerSubring (idem_e : IsIdempotentElem e) := CornerSubringNonUnital e

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

-- The corner ring is a ring
instance CornerRingIsRing (idem_e : IsIdempotentElem e) : Ring (CornerSubring idem_e) := non_unital_w_e_is_ring 1 (is_left_unit idem_e) (is_right_unit idem_e) -- Done by Job


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



def ideal_push (idem_e : IsIdempotentElem e) (J : Ideal R) : Ideal (CornerSubring idem_e) where -- Maša
  carrier := {x | ∃ y ∈ J, x = e * y * e}
  zero_mem' := by
    use 0
    constructor
    · exact Submodule.zero_mem J
    · simp
  add_mem' := by
    rintro x y ⟨r, ⟨hr_mem, hr⟩⟩ ⟨s, ⟨hs_mem, hs⟩⟩
    use r + s
    constructor
    · exact (Submodule.add_mem_iff_right J hr_mem).mpr hs_mem
    · simp [hr, hs]
      noncomm_ring
  smul_mem' := by
    rintro ⟨c, ⟨a, hc⟩⟩ x ⟨r, ⟨hr_mem, hr⟩⟩
    use a * e  * e * r
    constructor
    · exact Ideal.mul_mem_left J (a * e *e) hr_mem
    · simp [hc, hr]
      noncomm_ring




theorem push_pull (idem_e : IsIdempotentElem e) (I : Ideal (CornerSubring idem_e)) : ideal_push idem_e (ideal_lift idem_e I) = I := by -- Maša
  ext x
  constructor
  · rintro ⟨y, ⟨hy_mem, hy⟩⟩
    unfold ideal_lift at hy_mem

    sorry

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
      exact hx



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

-- if a and b in eRe, then a (e R e) = a R b as sets
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

lemma e_in_corner_ring : --Maša
  e ∈ (CornerSubring idem_e) := by
  rw [subring_mem_idem]
  rw [IsIdempotentElem.eq idem_e, IsIdempotentElem.eq idem_e]

lemma nonzero (x : CornerSubring idem_e) (hx : x.val ≠ 0): (x : CornerSubring idem_e) ≠ 0 := by
  by_contra hzero
  rw [Subtype.ext_iff_val] at hzero
  exact hx hzero

lemma eq_iff_val (x y z : CornerSubring idem_e) : (x + y).val = z.val ↔ x.val + y.val = z.val := by
  exact Eq.congr_right rfl
