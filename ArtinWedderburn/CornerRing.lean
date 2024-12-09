import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing

variable {R : Type*} [Ring R]
variable (I J : Ideal R) -- Ideals in mathlib are LEFT ideals (defined as Submodule R R)
variable (A B C: Set R)
variable {e f : R}

def CornerRingSet (idem_e : IsIdempotentElem e) : Set R := (e ⬝ R ⬝ e)

variable (idem_e : IsIdempotentElem e)

-- an element x of R is in the corner ring if and only if x = e * x * e
theorem x_in_corner_x_eq_e_x_e (x : R) : x ∈ CornerRingSet idem_e ↔ x = e * x * e := by -- Done by Job
  constructor
  {rintro ⟨x, rfl⟩; rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, idem_e]; rw [← mul_assoc e x e, ← mul_assoc e (e *x) e, ← mul_assoc e e x, idem_e]}
  {intro hx; use x;symm;assumption}

theorem x_in_corner_x_eq_e_y_e (x : CornerRingSet idem_e): ∃ (y : R), x = e * y * e := by
  use x.val
  exact (x_in_corner_x_eq_e_x_e idem_e x.val).1 x.property

variable (A : Set R)
variable (x : R)
variable (h : x ∈ A)

-- CornerRing as a subtype of R
def CornerRing := {x : R // x ∈ CornerRingSet idem_e}

-- in the corner ring e is the identity element
theorem e_left_unit (a : CornerRing idem_e) : e * a.val = a.val := by -- Done by Job
  rw [(x_in_corner_x_eq_e_x_e idem_e a.val).1 a.property, ← mul_assoc, ← mul_assoc, idem_e]

theorem e_right_unit (a : CornerRing idem_e) : a.val * e = a.val := by
  rw [(x_in_corner_x_eq_e_x_e idem_e a.val).1 a.property, mul_assoc, mul_assoc, idem_e, mul_assoc]

theorem a_b_in_corner_prod_in_corner (a b : CornerRing idem_e) : a.val * b.val ∈ CornerRingSet idem_e := by
  use a.val * b.val
  rw [←mul_assoc, e_left_unit, mul_assoc, e_right_unit]


instance : NonUnitalSubring R where -- Done by Matevz
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

-- Multiplication strucure is inherited from R
instance : Mul (CornerRing idem_e) := {mul := λ a b => ⟨a.val * b.val, a_b_in_corner_prod_in_corner idem_e a b⟩}

-- this is a ring
instance: Ring (CornerRing idem_e) := by sorry -- Matevz

-- Lemma 2.10
-- a) If R is artinian, then the corner ring is artinian
theorem corner_ring_artinian [IsArtinian R R] : IsArtinian (CornerRing idem_e) (CornerRing idem_e) := by sorry -- Mikita

-- b) If R is a prime ring, then the corner ring is prime
theorem corner_ring_prime (h : IsPrimeRing R) : IsPrimeRing (CornerRing idem_e) := by sorry -- Job
