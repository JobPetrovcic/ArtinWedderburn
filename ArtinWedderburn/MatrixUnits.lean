import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing

-- TODO: maybe split this up into multiple definitions
class hasMatrixUnits (R : Type*) [Ring R] (n : ℕ) where -- Done by Job
  es : Fin n → Fin n → R
  diag_sum_eq_one : ∑ i, es i i = 1
  mul_ij_kl_eq_kron_delta_jk_mul_es_il : ∀ i j k l, es i j * es k l = (if j = k then es i l else 0)

open hasMatrixUnits

variable (R : Type*) [Ring R]
variable {n : ℕ} {hn : 0 < n} [mu : hasMatrixUnits R n]

abbrev e00_idem : IsIdempotentElem (mu.es ⟨0, hn⟩ ⟨0, hn⟩) := mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩

abbrev e00_cornerring := CornerSubring (@e00_idem R _ n hn mu )

lemma e00_cornerring_1 : (1 : CornerSubring (@e00_idem R _ n hn mu )) = mu.es ⟨0, hn⟩ ⟨0, hn⟩ := by rfl

lemma e00e0i_eq_e_0i (i : Fin n) : mu.es ⟨0, hn⟩ ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i = mu.es ⟨0, hn⟩ i := by rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il];simp

lemma ei0e00_eq_e_ei0 (i : Fin n) : mu.es i ⟨0, hn⟩* mu.es  ⟨0, hn⟩ ⟨0, hn⟩ = mu.es i ⟨0, hn⟩ := by rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il]; simp only [↓reduceIte]

lemma ei0e0j_eq_eij (i j : Fin n) : mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j = mu.es i j := by rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il]; simp only [↓reduceIte]

def ij_corner (i j : Fin n) (a : R) : @CornerSubring R _ _ (@e00_idem R _ n hn mu) := ⟨es ⟨0, hn⟩ i  * a * es j ⟨0, hn⟩,
  by rw [subring_mem_idem , ←mul_assoc, ←mul_assoc, e00e0i_eq_e_0i, mul_assoc, mul_assoc, mul_assoc, ei0e00_eq_e_ei0]⟩


abbrev matrix_corner := Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu)

-- define the map from R to matrix ring by a ↦ e_{0i}ae_{j0} for all i, j
def ring_to_matrix_ring (n : ℕ) (hn : 0 < n)(mu : hasMatrixUnits R n) : R → Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) := fun a => λ i j => (ij_corner R i j a)

-- show that this map is additive
theorem ring_to_matrix_ring_additive
  (a b : R)
  : (ring_to_matrix_ring R n hn mu) (a + b) = (ring_to_matrix_ring R n hn mu) a + (ring_to_matrix_ring R n hn mu) b := by
  ext i j
  unfold ring_to_matrix_ring
  simp [ij_corner]
  noncomm_ring


theorem matrixunit_iz_zi_eq_ii : ∀ i : Fin n, es i i = (mu.es i ⟨0, hn⟩) * (mu.es ⟨0, hn⟩ i) := by
  intro i
  rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il i ⟨0, hn⟩ ⟨0, hn⟩ i]
  simp

-- if a ring has matrix units then 1 = sum_i e_i0e0i
theorem one_eq_sum_es_00e_00e (n : ℕ)(hn : 0 < n)(mu : hasMatrixUnits R n) : 1 = ∑ i, mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i := by
  rw [← mu.diag_sum_eq_one]
  have h (i : Fin n) : mu.es i i = (mu.es i ⟨0, hn⟩) * (mu.es ⟨0, hn⟩ i) := by
    exact matrixunit_iz_zi_eq_ii R i
  simp [h]

theorem _lift_sum (f : Fin n → (@e00_cornerring R _ n hn mu)) : ((∑ i : Fin n, f i : (@e00_cornerring R _ n hn mu)) : R) = ∑ i : Fin n, (f i : R) := by exact AddSubmonoidClass.coe_finset_sum f Finset.univ

-- show that this map is multiplicative
theorem ring_to_matrix_ring_multiplicative (a b : R)
  : (ring_to_matrix_ring R n hn mu) (a * b) = (ring_to_matrix_ring R n hn mu) a * (ring_to_matrix_ring R n hn mu) b := by
  ext i j
  unfold ring_to_matrix_ring
  have hab : a * b = a * 1 * b := by simp
  rw [hab]
  -- expand the 1
  rw [one_eq_sum_es_00e_00e R n hn mu]
  -- unfold the definition of matrix multiplication
  simp [Matrix.mul_apply]
  -- put the a inside the sum
  unfold ij_corner
  apply Subtype.eq
  simp only [MulMemClass.mk_mul_mk]

  calc
    es ⟨0, hn⟩ i * ((a * ∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * b) * es j ⟨0, hn⟩ = (es ⟨0, hn⟩ i * a) * (∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * (b* es j ⟨0, hn⟩) := by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    _ = (∑ i_1 : Fin n, es ⟨0, hn⟩ i * a * (es i_1 ⟨0, hn⟩ * es ⟨0, hn⟩ i_1)) * (b * es j ⟨0, hn⟩) := by
      rw [Finset.mul_sum Finset.univ]
    _ = (∑ i_1 : Fin n, es ⟨0, hn⟩ i * a * (es i_1 ⟨0, hn⟩ * es ⟨0, hn⟩ i_1) * (b * es j ⟨0, hn⟩)) := by rw [Finset.sum_mul]
    _ = ∑ j_1 : Fin n, es ⟨0, hn⟩ i * a * es j_1 ⟨0, hn⟩ * (es ⟨0, hn⟩ j_1 * b * es j ⟨0, hn⟩) := by {
      apply Finset.sum_congr
      simp
      intro x hx
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    }

  symm
  rw [_lift_sum]

def matrix_one : (1 : Matrix (Fin n) (Fin n) R) = (fun i j => if i = j then 1 else 0):= by exact rfl

def corner_matrix_zero_equiv (a : R): (∀ (i j : Fin n), (es i i) * a * (es j j) = 0) ↔ a = 0 := by
  constructor
  {
    intro hij
    have h : ∀ (i : Fin n), (es i i) * a = 0 := by
      have a1 : a = a * 1 := by simp
      rw [a1, ←mu.diag_sum_eq_one]
      intro i
      rw [Finset.mul_sum Finset.univ, Finset.mul_sum Finset.univ]
      simp only [mul_assoc] at hij
      simp only [hij]
      apply Fintype.sum_eq_zero
      simp
    have hs : ∑ (i : Fin n), (es i i) * a = 0 := by simp only [h]; exact Fintype.sum_eq_zero (fun a ↦ 0) (congrFun rfl)
    rw [←Finset.sum_mul Finset.univ] at hs
    rw [mu.diag_sum_eq_one] at hs
    simp only [one_mul] at hs
    exact hs
  }
  {
    intro h
    rw [h]
    simp only [mul_zero, zero_mul, implies_true]
  }

def corner_matrix_zero_crit (a : R) : (∀ (i j : Fin n), @ij_corner R _ n hn mu i j a = 0 )→ a = 0 := by
  rw [←(@corner_matrix_zero_equiv R _ n)]

  intro h
  unfold ij_corner at h
  intro i j
  have h' : (mu.es i ⟨0, hn⟩ * (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) * mu.es ⟨0, hn⟩ j) = 0 := by
    have l := h i j
    have l': (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) = 0 := by exact congrArg Subtype.val l
    simp only [l']
    simp only [mul_zero, zero_mul]
  have h'' : (mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i) * a * (mu.es j ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j) = 0 := by
    rw [←h']
    repeat rw [mul_assoc]
  simp only [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il i ⟨0, hn⟩ ⟨0, hn⟩ i] at h''
  simp only [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il j ⟨0, hn⟩ ⟨0, hn⟩ j] at h''
  simp  at h''
  exact h''


def ring_to_matrix_ring_hom: R →+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) :=
{
  toFun := ring_to_matrix_ring R n hn mu,
  map_one' := by
    ext i j
    simp only [SetLike.coe_eq_coe]
    unfold ring_to_matrix_ring ij_corner
    simp only [mul_one]
    simp only [matrix_one (@e00_cornerring R _ n hn mu)]
    have h := mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ i j ⟨0, hn⟩
    simp only [h]
    split_ifs
    rfl
    rfl
  map_add' := ring_to_matrix_ring_additive R
  map_mul' := ring_to_matrix_ring_multiplicative R
  map_zero' := by
    ext i j
    simp only [Matrix.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero]
    unfold ring_to_matrix_ring ij_corner
    simp only [mul_zero, zero_mul]
    rfl
}

-- define the reverse map from matrix ring to R
def matrix_to_ring (n : ℕ)(hn : 0 < n)(mu : hasMatrixUnits R n) : Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) → R := fun M => ∑ i, ∑ j, (mu.es i ⟨0, hn⟩) * M i j * (mu.es ⟨0, hn⟩ j)

-- lemma: multiplying e0k with ∑ ei0 f i = e0k ek0 fk  = e00 f k
lemma e0k_left_mul_sum {k : Fin n} {f : Fin n → R} : mu.es ⟨0, hn⟩ k * ∑ i, mu.es i ⟨0, hn⟩ * f i = mu.es ⟨0, hn⟩ ⟨0, hn⟩ * f k := by
  rw [Finset.mul_sum]
  have hif : ∀ i, es ⟨0, hn⟩ k * (es i ⟨0, hn⟩ * f i) = if k=i then es ⟨0, hn⟩ ⟨0, hn⟩ * f k else 0 := by intro i; rw [←mul_assoc, mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ k i ⟨0, hn⟩]; split_ifs with h; simp only[h]; simp only [zero_mul]
  simp only [hif]
  exact Fintype.sum_ite_eq k fun j ↦ es ⟨0, hn⟩ ⟨0, hn⟩ * f k
-- same but now from the right: ∑ f i e0i and ek0 = fk e0k ek0 = f k e00
lemma right_mul_sum_e0k {k : Fin n} {f : Fin n → R} : (∑ i, f i * mu.es ⟨0, hn⟩ i) * mu.es k ⟨0, hn⟩ = f k * mu.es ⟨0, hn⟩ ⟨0, hn⟩ := by
  rw [Finset.sum_mul]
  have hif : ∀ i, (f i * mu.es ⟨0, hn⟩ i) * mu.es k ⟨0, hn⟩ = if i=k then f k * mu.es ⟨0, hn⟩ ⟨0, hn⟩ else 0 := by intro i; rw [mul_assoc,  mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ i k ⟨0, hn⟩]; split_ifs with h; simp only[h]; simp only [mul_zero]
  simp only [hif]
  exact Fintype.sum_ite_eq' k fun j ↦ f k * es ⟨0, hn⟩ ⟨0, hn⟩

-- with these two lemmas we can show that matrix_to


lemma matrixcorner1 : (1 : Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu)) = (λ i j => if i = j then (1 : (@e00_cornerring R _ n hn mu)) else 0) := by exact rfl

--def matrix_to_ring_hom : Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) →+* R :=
--{
--  toFun := matrix_to_ring R n hn mu,
--  map_one' := by
--    unfold matrix_to_ring
--    have h : ∀ i j, (mu.es i ⟨0, hn⟩) * (if i = j then (1 : R) else 0) * (mu.es ⟨0, hn⟩ j) = if i = j then mu.es i i else 0 := by
--      intro i j
--      split_ifs with h
--      rw [h]
--      simp only [mul_one]
--      rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il j ⟨0, hn⟩ ⟨0, hn⟩ j ]
--      simp only [↓reduceIte]
--      simp only [mul_zero, zero_mul]
--    rw [matrixcorner1]
--    simp only
--    calc
--      _ = ∑ x : Fin n, ∑ x_1 : Fin n, if x = x_1 then mu.es x x_1 else 0 := by
--        apply Finset.sum_congr
--        rfl
--        intro i hj
--        apply Finset.sum_congr
--        rfl
--        intro j hj
--        split_ifs with h''
--        rw [e00_cornerring_1, ei0e00_eq_e_ei0, ei0e0j_eq_eij]
--
--        simp only [ZeroMemClass.coe_zero, mul_zero, zero_mul]
--      _ = ∑ x : Fin n, mu.es x x := by apply Finset.sum_congr ;simp;intro x hx;exact Fintype.sum_ite_eq x (es x)
--      _ = 1 := by exact mu.diag_sum_eq_one
--  map_mul' := by
--    intro A B
--    simp only
--    unfold matrix_to_ring
--    sorry
--  map_add' := by sorry
--  map_zero' := by
--    simp only [RingHom.map_zero]
--    unfold matrix_to_ring
--    simp only [Matrix.zero_apply, ZeroMemClass.coe_zero, mul_zero, zero_mul, Finset.sum_const_zero]
--}

lemma e00_unit (a : @e00_cornerring R _ n hn mu) : mu.es ⟨0, hn⟩ ⟨0, hn⟩ * (a : R) = a := by
  have h : 1 * a = a := by simp only [one_mul]
  nth_rewrite 2 [←h]
  rfl
lemma unit_e00 (a : @e00_cornerring R _ n hn mu) : (a : R) * mu.es ⟨0, hn⟩ ⟨0, hn⟩ = a := by
  have h : a * 1 = a := by simp only [mul_one]
  nth_rewrite 2 [←h]
  rfl

noncomputable
def ring_to_matrix_iso [mu : hasMatrixUnits R n] : R ≃+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) := by

  apply RingEquiv.ofBijective (ring_to_matrix_ring_hom R)
  constructor
  {
    refine (injective_iff_map_eq_zero (ring_to_matrix_ring_hom R)).mpr ?left.a
    intro a
    simp only [ring_to_matrix_ring_hom]
    unfold ring_to_matrix_ring
    simp
    intro h
    apply (@corner_matrix_zero_crit R _ n)
    intro i j
    have fn_lemma  {α β} {f g : α → β}( h : f = g) (a : α) : f a = g a := by rw [h]
    have h := fn_lemma h i
    exact fn_lemma h j
  }
  {
    intro A
    let a : R := ∑ i, ∑ j, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j)
    use a
    simp [ring_to_matrix_ring_hom]
    unfold ring_to_matrix_ring
    ext i j
    unfold ij_corner
    simp only [a]
    have h : (es ⟨0, hn⟩ i * ∑ i : Fin n, ∑ j : Fin n, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j)) = (es ⟨0, hn⟩ i * ∑ i : Fin n, es i ⟨0, hn⟩ * ∑ j : Fin n, ((A i j : R) * es ⟨0, hn⟩ j)) := by rw [Finset.sum_congr]; rfl; intro i hi; rw [Finset.mul_sum];
    rw [h,e0k_left_mul_sum]
    simp only [mul_assoc]
    rw [right_mul_sum_e0k]
    simp only [unit_e00, e00_unit]
  }



-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11
noncomputable
def ring_with_matrix_units_isomorphic_to_matrix_ring (n : ℕ) (hn : 0 < n)(mu : hasMatrixUnits R n) :
  R ≃+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) := ring_to_matrix_iso R
