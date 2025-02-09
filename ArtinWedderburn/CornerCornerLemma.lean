import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.Algebra.Ring.Equiv
import ArtinWedderburn.CornerRing
import ArtinWedderburn.Idempotents

variable {R : Type*} [Ring R]

lemma val_mul_subring (S : NonUnitalSubring R) (a b : S) : (a * b : S) = a.val * b.val := by simp only [NonUnitalSubring.val_mul]

-- theorem: if we have a non unital subring S of R and a non unital subring A of S, and a non unital subring B of R that has the same elements as A, then A is isomorphic to B
def non_unital_subring_eq
  {S : NonUnitalSubring R}
  [Ring S]
  -- the addition and multiplication of S are the same as the addition and multiplication of R
  (ha : ∀ x y : ↥S, (x + y : ↥S) = x.val + y.val)
  (hs : ∀ x y : ↥S, (x * y : ↥S) = x.val * y.val)
  {A : NonUnitalSubring S}
  {B : NonUnitalSubring R}
  (h : (Subtype.val '' A.carrier) = B.carrier)
  : A ≃+* B := by
  have h' (x : R) : x ∈ B ↔ x ∈ Subtype.val '' A.carrier := by rw [h]; rfl
  have h'' (b : B) : b.val ∈ S := by
    have hx : b.val ∈ Subtype.val '' A.carrier := by rw [← h']; exact b.property
    obtain ⟨w, ⟨ca, weqb⟩⟩ := hx
    rw [← weqb]
    exact w.property
  have h''' (b : B) : ⟨b.val, h'' b⟩ ∈ A := by
    have hx : b.val ∈ Subtype.val '' A.carrier := by rw [← h']; exact b.property
    obtain ⟨w, ⟨ca, weqb⟩⟩ := hx
    simp [←weqb]
    exact ca

  exact {
    toFun := fun a => ⟨
      a.val, by rw [h']; simp
    ⟩
    invFun := fun b => ⟨⟨b, by apply h''⟩, by apply h'''⟩
    left_inv := by intro a; simp,
    right_inv := by intro b; simp,
    map_mul' := by
      intro a b
      simp
      rw [hs a b]
    map_add' := by
      simp [ha]
  }

-- with these we can prove the following lemma
-- if e is an idempotent element of R, and f is an idempotent element of the corner ring of e, then the CornerSubringNonUnital of f.val is isomorphic to the CornerSubringNonUnital of f of the corner ring of e

variable {R : Type*} [Ring R]
variable {e : R}
variable {idem_e : IsIdempotentElem e}
variable (f : CornerSubring idem_e)

set_option synthInstance.maxHeartbeats 5000000


theorem double_corner_set_eq : (Subtype.val '' (CornerSubringNonUnital f).carrier) = (CornerSubringNonUnital (f : R)).carrier := by
  rw [corner_ring_carrier, corner_ring_carrier]
  ext x
  constructor
  intro hx
  obtain ⟨y, ⟨hy, rfl⟩⟩ := hx
  obtain ⟨z, ⟨hz, rfl⟩⟩ := hy
  simp
  use z

  intro hx
  obtain ⟨y, ⟨hy, rfl⟩⟩ := hx

  let a : CornerSubring idem_e := ⟨e * y * e, by {use y}⟩
  use f * a * f
  constructor
  {use a}
  simp
  have h1f : f = 1 * f  := by simp
  have heff : e * (f : R) = f := by nth_rewrite 2 [h1f]; rfl
  have hf1 : f = f * 1 := by simp
  have hffe : f = f * e := by nth_rewrite 1 [hf1]; rfl
  rw [mul_assoc, mul_assoc, heff, ←mul_assoc, ←mul_assoc, ←hffe]

def corner_ring_eq_lemma (h : (Subtype.val '' (CornerSubringNonUnital f).carrier) = (CornerSubringNonUnital (f : R)).carrier) : CornerSubringNonUnital f ≃+* CornerSubringNonUnital (f : R) := by
  exact @non_unital_subring_eq R _ (CornerSubring idem_e) _ (by simp) (by simp) (CornerSubringNonUnital f ) (CornerSubringNonUnital (f : R)) h

def corner_ring_non_unital_eq : CornerSubringNonUnital f ≃+* CornerSubringNonUnital (f : R) := by
  apply corner_ring_eq_lemma
  apply double_corner_set_eq

variable {f : CornerSubring idem_e}
variable (idem_f : IsIdempotentElem f)

def corner_ring_unital_eq : CornerSubring idem_f ≃+* CornerSubring (e_idem_to_e_val_idem idem_f) := by
  unfold CornerSubring
  apply corner_ring_non_unital_eq
