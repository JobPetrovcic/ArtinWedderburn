import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.MinimalAxioms

variable {R : Type*} [NonUnitalRing R]
variable (e : R)

instance e_one: One R := ⟨e⟩

variable (is_left_unit : ∀ x : R, e * x = x)
variable (is_right_unit : ∀ x : R, x * e = x)


instance non_unital_w_e_is_ring: Ring R := @Ring.ofMinimalAxioms R (by exact inferInstance) (by exact inferInstance) (by exact inferInstance) (by exact inferInstance) (by exact e_one e) (by intro a b c; rw [add_assoc]) (by intro a; exact AddZeroClass.zero_add a) (by intro a; exact neg_add_cancel a) (by intro a b c;exact mul_assoc a b c) (is_left_unit) (is_right_unit) (by intro a b c; exact LeftDistribClass.left_distrib a b c) (by intro a b c;exact RightDistribClass.right_distrib a b c)
