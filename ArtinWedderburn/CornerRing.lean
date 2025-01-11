import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.NonUnitalToUnital
import Mathlib.Algebra.Ring.MinimalAxioms
import ArtinWedderburn.PrimeRing

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

-- Lemma 2.10
-- a) If R is artinian, then the corner ring is artinian
theorem corner_ring_artinian [IsArtinian R R] : IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by sorry -- Mikita

-- coercions from Sets of CornerSubrings to Set of R
instance : CoeOut (Set (CornerSubring idem_e)) (Set R) := {coe := fun X => Set.image Subtype.val X}

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
    rw [←is_right_unit idem_e ↑x] at hs
    rw [←is_left_unit idem_e ↑y] at hs
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
    rw [←both_mul_lift]
    rw [congrArg (Set.image Subtype.val) h]
    simp
  have l := prime_ring_equiv.1 hRP _ _ h_lift
  simp at l
  exact l
