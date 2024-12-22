import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.NonUnitalToUnital
import Mathlib.Algebra.Ring.MinimalAxioms

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

-- b) If R is a prime ring, then the corner ring is prime
theorem corner_ring_prime (h : IsPrimeRing R) : IsPrimeRing (CornerSubring idem_e) := by sorry -- Job
