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

def CornerRingSet (idem_e : IsIdempotentElem e) : Set R := (e ⬝ R ⬝ e)

variable (idem_e : IsIdempotentElem e)

-- an element x of R is in the corner ring if and only if x = e * x * e
theorem corner_ring_set_mem {x : R} : x ∈ CornerRingSet idem_e ↔ x = e * x * e := by -- Done by Job
  constructor
  {rintro ⟨x, rfl⟩; rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, idem_e]; rw [← mul_assoc e x e, ← mul_assoc e (e *x) e, ← mul_assoc e e x, idem_e]}
  {intro hx; use x;symm;assumption}

theorem x_in_corner_x_eq_e_y_e (x : CornerRingSet idem_e): ∃ (y : R), x = e * y * e := by
  use x.val
  exact (corner_ring_set_mem idem_e).1 x.property

instance CornerSubring : NonUnitalSubring R where -- Done by Matevz
  carrier := CornerRingSet idem_e
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r + s
    rw [← hr,  ← hs]
    noncomm_ring
  neg_mem' := by
    rintro x ⟨r, hr⟩
    use -r
    rw [← hr]
    noncomm_ring
  mul_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r * e * e * s
    rw [← hr, ← hs]
    noncomm_ring

variable {idem_e : IsIdempotentElem e}

variable {x : R}

theorem subring_mem : x ∈ CornerSubring idem_e ↔ x = e * x * e := by
  rw [← corner_ring_set_mem idem_e]; rfl

theorem corner_ring_both_mul_mem (x w y : R) (hx : x ∈ CornerSubring idem_e) (hy : y ∈ CornerSubring idem_e): (x * w * y) ∈ CornerSubring idem_e := by
  rw [subring_mem] at *
  rw [hx, hy]
  simp only [mul_assoc]
  rw [idem_e]
  simp only [←mul_assoc]
  rw [idem_e]


theorem left_unit_mul (h : x ∈ CornerSubring idem_e): e * x = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [←mul_assoc, ←mul_assoc, idem_e]

theorem right_unit_mul (h : x ∈ CornerSubring idem_e): x * e = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [mul_assoc, mul_assoc, idem_e, mul_assoc]

open NonUnitalSubringClass

abbrev CornerSubringIsRing (idem_e : IsIdempotentElem e) := toNonUnitalRing (CornerSubring (idem_e : IsIdempotentElem e))

theorem corner_ring_hom (a b : CornerSubring idem_e) : (a * b : CornerSubring idem_e) = (a : R) * (b : R) := by rfl

instance CornerRingOne: One (CornerSubring idem_e) := ⟨⟨e, by rw [subring_mem]; rw [idem_e, idem_e]⟩⟩

theorem corner_ring_one : (1 : CornerSubring idem_e) = e := by rfl
#check (CornerSubring idem_e)

#check @Ring.ofMinimalAxioms
#check (CornerSubringIsRing idem_e).mul_assoc

theorem is_left_unit : ∀ (x : CornerSubring idem_e), 1 * x = x := by -- Done by Job
  rw [Subtype.forall]
  intro a hx
  apply Subtype.eq
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, left_unit_mul hx]
theorem is_right_unit : ∀ (x : CornerSubring idem_e), x * 1 = x := by -- Done by Job
  rw [Subtype.forall]
  intro a hx
  apply Subtype.eq
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, right_unit_mul hx]

-- The corner ring is a ring
instance CornerRingIsRing (idem_e : IsIdempotentElem e) : Ring (CornerSubring idem_e) := non_unital_w_e_is_ring 1 is_left_unit is_right_unit -- Done by Job

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
    rw [←is_right_unit ↑x] at hs
    rw [←is_left_unit ↑y] at hs
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
