import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotents
import ArtinWedderburn.PrimeRing
import ArtinWedderburn.CornerRing
import ArtinWedderburn.SetProd
import ArtinWedderburn.MinIdeals


variable {R : Type*} [Ring R]
variable (I J : Ideal R)
variable {e f : R}


def IsOrthogonal (e f : R) : Prop := e * f = 0 ∧ f * e = 0

def AreOrthogonalIdempotents (e f : R) : Prop := IsIdempotentElem e ∧ IsIdempotentElem f ∧ IsOrthogonal e f


theorem leq_neq_lt (I J : Ideal R) : I ≤ J → I ≠ J → I < J := by -- Done by Matevz
  intro hleq hneq
  constructor
  · exact hleq
  · intro heq
    have h : I = J := by exact le_antisymm hleq heq
    trivial

-- Lemma 2.9
-- #HARDER
theorem one_sub_e_larger_span_on_sub_e_sub_f (e f : R) (ef_ort_idem : AreOrthogonalIdempotents e f) (fnz : f ≠ 0) : Ideal.span {1 - e - f} < Ideal.span {1 - e} := by -- Done by Matevz
  have hleq : Ideal.span {1 - e - f} ≤ Ideal.span {1 - e} := by
    apply Ideal.span_le.mpr
    intro x hx
    simp at hx
    rw [hx]
    simp
    have factor : (1 - e - f) * (1 - e) = 1 - e - f := by calc
      (1 - e - f) * (1 - e) = 1 - e - f - e + (e * e) + (f * e) := by noncomm_ring
      _ = 1 - e - f - e + e + 0 := by rw [ef_ort_idem.left, ef_ort_idem.right.right.right]
      _ = 1 - e - f := by noncomm_ring
    rw [Eq.symm factor]
    have in_span : 1 - e ∈ Ideal.span {1 - e} := by exact Ideal.mem_span_singleton_self (1 - e)
    exact Ideal.mul_mem_left (Ideal.span {1 - e}) (1 - e - f) in_span
  have hneq : Ideal.span {1 - e - f} ≠ Ideal.span {1 - e} := by
    intro heq
    have f_in_ideal : f ∈ Ideal.span {1 - e} := by
      have fact_f : f = f * (1 - e) := by calc
        f = f - f * e := by rw [ef_ort_idem.right.right.right]; noncomm_ring
        _ = f * (1 - e) := by noncomm_ring
      rw [fact_f]
      exact Ideal.mul_mem_left (Ideal.span {1 - e}) f (Ideal.mem_span_singleton_self (1 - e))
    rw [← heq] at f_in_ideal
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp f_in_ideal
    have fz : f = 0 := by calc
      f = r * (1 - e - f) := by rw [hr]
      _ = r * (1 - e - f - f + e * f + f * f) := by rw [ef_ort_idem.right.right.left, ef_ort_idem.right.left]; noncomm_ring
      _ = r * (1 - e - f) * (1 - f) := by noncomm_ring
      _ = f - f * f := by rw [hr]; noncomm_ring
      _ = 0 := by rw[ef_ort_idem.right.left]; noncomm_ring
    contradiction
  exact leq_neq_lt (Ideal.span {1 - e - f}) (Ideal.span {1 - e}) hleq hneq

theorem e_span_larger_e_sub_f (e f : R) (h : AreOrthogonalIdempotents (1 - e) f) (fnz : f ≠ 0): Ideal.span {e - f} <  Ideal.span {e} := by -- Maša
  have h' := one_sub_e_larger_span_on_sub_e_sub_f (1 - e) f h fnz
  simp at h'
  exact h'

def HasMatrixUnits (R : Type*) [Ring R] (n : ℕ) : Prop := ∃ (es : Fin n → Fin n → R), (∑ i, es i i = 1) ∧ (∀ i j k l, es i j * es k l = (if j = k then es i l else 0)) -- Done by Job (as class - see above) and rewritten by Matevz (as def)



def kronecker_delta (n : ℕ) (i j : Fin n) : R :=
  if i = j then 1 else 0

-- Lemma 2.18
-- hypothesis: we have a parwise orthogonal idempotent e_ii for each i in {1, ..., n}
-- and e1i ∈ e11Reii for all i in {2, ..., n}
-- and e1iei1 = e11 and ei1e1i = eii for all i in {2, ..., n}
-- conclusion: has matrix units R

def PairwiseOrthogonal (a b : R) : Prop := a * b = 0 ∧ b * a = 0

theorem OrtIdem_imply_MatUnits {n : ℕ} (hn : 0 < n) -- Done by Matevz
  (diag_es : Fin n → R)
  (idem : (∀ i : Fin n, IsIdempotentElem (diag_es i))) -- idempotent
  (ort : (∀ i j : Fin n, i ≠ j → PairwiseOrthogonal (diag_es i) (diag_es j))) -- pairwise orthogonal
  (sum_eq_one : ∑ i, diag_es i = 1) -- sum of diagonal elements is 1
  -- first row
  (row_es : Fin n -> R)
  (row_in : ∀ i : Fin n, row_es i ∈ both_mul (diag_es ⟨0, hn⟩) (diag_es i))
  -- first column
  (col_es : Fin n -> R)
  (col_in : ∀ i : Fin n, col_es i ∈ both_mul (diag_es i) (diag_es ⟨0, hn⟩))
  -- they are compatible
  (comp1 : ∀ i, row_es i * col_es i = diag_es ⟨0, hn⟩)
  (comp2 : ∀ i, col_es i * row_es i = diag_es i)
  : HasMatrixUnits R n := by
  use fun i j => (col_es i) * (row_es j)
  constructor
  · simp_rw [comp2]
    exact sum_eq_one
  · intro i j k l
    split_ifs with h
    · rw [h]
      have col_mul_diag : col_es i * diag_es ⟨0, hn⟩ = col_es i := by
        obtain ⟨r, hr⟩ := col_in i
        calc
          col_es i * diag_es ⟨0, hn⟩ = diag_es i * r * (diag_es ⟨0, hn⟩ * diag_es ⟨0, hn⟩) := by rw [hr]; noncomm_ring
          _ = diag_es i * r * diag_es ⟨0, hn⟩ := by rw [idem ⟨0, hn⟩]
          _ = col_es i := by rw [hr]
      calc
        (col_es i * row_es k) * (col_es k * row_es l) = col_es i * (row_es k * col_es k) * row_es l := by noncomm_ring
        _ = col_es i * diag_es ⟨0, hn⟩ * row_es l := by rw [comp1 k]
        _ = col_es i * row_es l := by rw [col_mul_diag]
    · obtain ⟨r, hr⟩ := row_in j
      obtain ⟨s, hs⟩ := col_in k
      calc
        (col_es i * row_es j) * (col_es k * row_es l) = col_es i * (diag_es ⟨0, hn⟩ * r * (diag_es j * diag_es k) * s * diag_es ⟨0, hn⟩) * row_es l := by rw [hr, hs]; noncomm_ring
        _ = 0 := by rw [(ort j k h).left]; noncomm_ring




-- If e and f are nonzero elements then corner ring eRf contains nonzero element
lemma eRf_nonzero --Maša
  (h : IsPrimeRing R) (e f : R) (he : e ≠ 0) (hf : f ≠ 0) :
  ∃(a : R), e * a * f ≠ 0 := by
  by_contra ha
  push_neg at ha
  have eRf_zero : both_mul e f = {0} := by
    ext x
    constructor
    · intro ⟨r, hr⟩
      specialize ha r
      exact Set.mem_of_eq_of_mem hr ha
    · intro hx
      use 0
      noncomm_ring
      exact hx
  apply prime_ring_equiv.1 h at eRf_zero
  cases eRf_zero with
  | inl h => exact he h
  | inr h => exact hf h


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

--multiplication with e and f preserves both_mul e f
lemma both_mul_e_f (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) :
  ∀ x ∈ both_mul e f, e * x = x ∧ x * f = x := by
  rintro x ⟨y, hy⟩
  have he : e * x = x := by
    calc _ = (e * e) * y * f := by rw [hy]; noncomm_ring
        _ = e * y * f := by rw [idem_e]
        _ = x := by exact id (Eq.symm hy)
  have hf : x * f = x := by
    calc _ = e * y * (f * f) := by rw [hy]; noncomm_ring
        _ = e * y * f := by rw [idem_f]
        _ = x := by exact id (Eq.symm hy)
  exact ⟨he, hf⟩

-- both_mul is closed for addition and multiplication
lemma both_mul_add : ∀ (x y : R), x ∈ both_mul e f → y ∈ both_mul e f → x + y ∈ both_mul e f := by
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a + b)
  rw [ha, hb]
  noncomm_ring

lemma both_mul_neg : ∀ (x : R), x ∈ both_mul e f → -x ∈ both_mul e f := by
  intro x ⟨a, ha⟩
  use - a
  rw [ha]
  noncomm_ring

lemma both_mul_sub : ∀ (x y : R), x ∈ both_mul e f → y ∈ both_mul e f → x - y ∈ both_mul e f := by
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a - b)
  rw [ha, hb]
  noncomm_ring

lemma both_mul_mul : ∀ (x y : R), x ∈ both_mul e f → y ∈ both_mul f e → x * y ∈ both_mul e e := by
  intro  x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a * f * f * b)
  rw [ha, hb]
  noncomm_ring

class two_nice_idempotents (e f : R) where
  (u : R)
  (v : R)
  (u_mem : u ∈ both_mul e f)
  (v_mem : v ∈ both_mul f e)
  (u_mul_v : u * v = e)
  (v_mul_u : v * u = f)

def lemma_2_19'(h : IsPrimeRing R)
  (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (ort : IsOrthogonal e f)
  (heRe : IsDivisionRing (CornerSubring idem_e)) (hfRf : IsDivisionRing (CornerSubring idem_f)) : two_nice_idempotents e f := by
  have he : e ≠ 0 := by exact corner_ring_division_e_nonzero idem_e heRe
  have hf : f ≠ 0 := by exact corner_ring_division_e_nonzero idem_f hfRf
  have ha : ∃ (a : R), e * a * f ≠ 0 := by exact eRf_nonzero h e f he hf
  obtain ⟨a, ha⟩ := by exact eRf_nonzero h e f he hf
  have hb : ∃(b : R), e * a * f * b * e ≠ 0 := by exact eRf_nonzero h (e * a * f) e ha he
  obtain ⟨b, hb⟩ := hb

  have hx : e * a * f * b * e ∈ CornerSubring idem_e := by
    rw [subring_mem_idem]
    rw [eq_comm]
    calc e * (e * a * f * b * e) * e = (e * e) * a * f * b * (e * e) := by noncomm_ring
        _ = e * a * f * b * e := by rw [IsIdempotentElem.eq idem_e]
        _ = e * a * f * b * e := by exact rfl

  let x : CornerSubring idem_e := ⟨e * a * f * b * e, hx⟩
  have x_val_eq : x.val = e * a * f * b * e := by rfl

  have x_nonzero : (x : CornerSubring idem_e) ≠ 0 := by
    rw [nonzero]
    rw [x_val_eq]
    exact hb

  have x_inv : ∃ (y : CornerSubring idem_e), x * y = (1 : CornerSubring idem_e) := by
    obtain ⟨_, h'⟩ := heRe
    specialize h' x x_nonzero
    obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := h'
    exact Exists.intro y hy₂

  obtain ⟨y, hy⟩ := x_inv

  let e_corner : CornerSubring idem_e := ⟨e, by exact e_in_corner_ring idem_e⟩
  have hxy : e_corner = (1 : CornerSubring idem_e) := by exact rfl
  have hxy : x * y = (e_corner : R):= by
    have hxy' : x * y = (e_corner : CornerSubring idem_e) := by exact hy
    rw [Subtype.ext_iff_val] at hxy'
    exact hxy'

  have hc : ∃ (c : R), y = e * c * e := by
    apply x_in_corner_x_eq_e_y_e y.2
  obtain ⟨c, hc⟩ := hc

  have y_val_eq : y.val = e * c * e := by exact hc

  let v := f * b * e * c * e
  let u := e * a * f
  use u
  use v

  have hu : u ∈ both_mul e f := by use a
  have hv : v ∈ both_mul f e := by
    have _ : f * b * e * c * e = f * (b * e * c) * e := by noncomm_ring
    use (b * e * c)

  have fv_eq_v : f * v = (v : R) := by exact (both_mul_e_f f idem_f idem_e v hv).1
  have ve_eq_v : v * e = v := by exact (both_mul_e_f f idem_f idem_e v hv).2

  have uv_eq_e : u * v = e := by
    calc e * a * f * (f * b * e * c * e) = e * a * (f * f) * b * e * c * e := by noncomm_ring
                                          _ = e * a *  f * b * e * c * e := by rw [IsIdempotentElem.eq idem_f]
                                          _ = e * a * f * b * (e * e) * c * e := by rw [IsIdempotentElem.eq idem_e]
                                          _ = (e * a * f * b * e) * (e * c * e) := by noncomm_ring
                                          _ = x * y := by rw [x_val_eq, y_val_eq]
                                          _ = e := by exact hxy

  have vuv_eq_v : v * u * v = v := by
    calc _ = v * (u * v) := by noncomm_ring
        _ = v * e := by rw [uv_eq_e]
        _ = v := by exact ve_eq_v
  sorry

-- Lemma 2.19 (a)
theorem lemma_2_19 -- Maša
  (h : IsPrimeRing R)
  (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (ort : IsOrthogonal e f)
  (heRe : IsDivisionRing (CornerSubring idem_e)) (hfRf : IsDivisionRing (CornerSubring idem_f)) :
  ∃ u v : R, u ∈ both_mul e f ∧ v ∈ both_mul f e ∧ u * v = e ∧ v * u = f := by
  have he : e ≠ 0 := by exact corner_ring_division_e_nonzero e idem_e heRe
  have hf : f ≠ 0 := by exact corner_ring_division_e_nonzero f idem_f hfRf
  have ha : ∃ (a : R), e * a * f ≠ 0 := by exact eRf_nonzero h e f he hf
  obtain ⟨a, ha⟩ := ha
  have hb : ∃(b : R), e * a * f * b * e ≠ 0 := by exact eRf_nonzero h (e * a * f) e ha he
  obtain ⟨b, hb⟩ := hb

  have hx : e * a * f * b * e ∈ CornerSubring idem_e := by
    rw [subring_mem_idem]
    rw [eq_comm]
    calc e * (e * a * f * b * e) * e = (e * e) * a * f * b * (e * e) := by noncomm_ring
        _ = e * a * f * b * e := by rw [IsIdempotentElem.eq idem_e]
        _ = e * a * f * b * e := by exact rfl

  let x : CornerSubring idem_e := ⟨e * a * f * b * e, hx⟩
  have x_val_eq : x.val = e * a * f * b * e := by rfl

  have x_nonzero : (x : CornerSubring idem_e) ≠ 0 := by
    rw [nonzero]
    rw [x_val_eq]
    exact hb

  have x_inv : ∃ (y : CornerSubring idem_e), x * y = (1 : CornerSubring idem_e) := by
    obtain ⟨_, h'⟩ := heRe
    specialize h' x x_nonzero
    obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := h'
    exact Exists.intro y hy₂

  obtain ⟨y, hy⟩ := x_inv

  let e_corner : CornerSubring idem_e := ⟨e, by exact e_in_corner_ring idem_e⟩
  have hxy : e_corner = (1 : CornerSubring idem_e) := by exact rfl
  have hxy : x * y = (e_corner : R):= by
    have hxy' : x * y = (e_corner : CornerSubring idem_e) := by exact hy
    rw [Subtype.ext_iff_val] at hxy'
    exact hxy'

  have hc : ∃ (c : R), y = e * c * e := by
    apply x_in_corner_x_eq_e_y_e y.2
  obtain ⟨c, hc⟩ := hc

  have y_val_eq : y.val = e * c * e := by exact hc

  let v := f * b * e * c * e
  let u := e * a * f
  use u
  use v

  have hu : u ∈ both_mul e f := by use a
  have hv : v ∈ both_mul f e := by
    have _ : f * b * e * c * e = f * (b * e * c) * e := by noncomm_ring
    use (b * e * c)

  have fv_eq_v : f * v = (v : R) := by exact (both_mul_e_f f idem_f idem_e v hv).1
  have ve_eq_v : v * e = v := by exact (both_mul_e_f f idem_f idem_e v hv).2

  have uv_eq_e : u * v = e := by
    calc e * a * f * (f * b * e * c * e) = e * a * (f * f) * b * e * c * e := by noncomm_ring
                                          _ = e * a *  f * b * e * c * e := by rw [IsIdempotentElem.eq idem_f]
                                          _ = e * a * f * b * (e * e) * c * e := by rw [IsIdempotentElem.eq idem_e]
                                          _ = (e * a * f * b * e) * (e * c * e) := by noncomm_ring
                                          _ = x * y := by rw [x_val_eq, y_val_eq]
                                          _ = e := by exact hxy

  have vuv_eq_v : v * u * v = v := by
    calc _ = v * (u * v) := by noncomm_ring
        _ = v * e := by rw [uv_eq_e]
        _ = v := by exact ve_eq_v


  constructor
  · exact hu
  · constructor
    · exact hv
    · constructor
      · exact uv_eq_e
      · by_contra h_neq
        push_neg at h_neq
        have h_nonzero : v * u - f ≠ 0 := by exact sub_ne_zero_of_ne h_neq
        have h_mem : v * u - f ∈ CornerSubring idem_f := by
          have vu_mem : v * u ∈ both_mul f f := by
            apply both_mul_mul
            exact hv
            exact hu
          have f_mem : f ∈ both_mul f f := by
            apply e_in_corner_ring idem_f
          apply both_mul_sub
          exact vu_mem
          exact f_mem
        let w : CornerSubring idem_f := ⟨v * u - f, h_mem⟩
        have w_val_eq : w.val = v * u - f := by exact rfl
        have h_inv : ∃(a : CornerSubring idem_f), a * w = (1 : CornerSubring idem_f) := by
          obtain ⟨a, ⟨h1, h2⟩⟩ := hfRf.2 w (by rw [nonzero]; exact h_nonzero)
          use a
        obtain ⟨a, ha⟩ := h_inv
        have wv_eq_zero : w * v = 0 := by
          calc _ = (v * u - f) * v := by exact rfl
              _ = v * u * v - f * v := by noncomm_ring
              _ = 0 := by rw[vuv_eq_v, fv_eq_v]; simp

        have v_eq_zero : v = 0 := by
          calc _ = (1 : CornerSubring idem_f) * v := by exact id (Eq.symm fv_eq_v)
              _ = (a * w) * v := by rw [← ha]; simp
              _ = a * (w * v) := by noncomm_ring
              _ = 0 := by rw[wv_eq_zero]; simp
        have e_eq_zero : e = 0 := by
          calc _ = u * v := by rw[uv_eq_e]
              _ = 0 := by rw[v_eq_zero]; noncomm_ring
        exact he e_eq_zero


theorem f_in_corner_othogonal (e f : R) (idem_e : IsIdempotentElem e) --Maša
  (f_mem : f ∈ both_mul (1 - e) (1 - e)) : IsOrthogonal e f := by
  obtain ⟨x, hx⟩ := f_mem
  constructor
  · rw [hx]
    calc _ = (e - e * e) * x * (1 - e) := by noncomm_ring
        _ = (e - e) * x * (1 - e) := by rw [idem_e]
        _ = 0 := by noncomm_ring
  · rw [hx]
    calc _ = (1 - e) * x * (e - e * e) := by noncomm_ring
        _ = (1 - e) * x * (e - e) := by rw [idem_e]
        _ = 0 := by noncomm_ring


lemma sum_orthogonal_idem_is_idem (e f : R) (h : AreOrthogonalIdempotents e f) : IsIdempotentElem (e + f) := by --Maša
  let ⟨idem_e, idem_f, h1, h2⟩ := h
  calc
    (e + f) * (e + f) = e * e + e * f + f * e + f * f := by noncomm_ring
    _ = e + 0 + 0 + f := by rw [idem_e, idem_f, h1, h2]
    _ = e + f := by simp

lemma prod_orthogonal_idem_is_idem (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (h : IsOrthogonal e f) : IsIdempotentElem (f * (1 - e)) := by --Maša
  unfold IsIdempotentElem
  calc _ = (f - (f * e)) * (f - (f * e)) := by noncomm_ring
      _ = f * f := by rw [h.2]; noncomm_ring
      _ = f - 0 := by rw[idem_f]; exact Eq.symm (sub_zero f)
      _ = f - f * e := by rw [h.2]
      _ = f * (1 - e) := by exact Eq.symm (mul_one_sub f e)

lemma e_f_orhogonal_f_1_sub_e_eq_f (e f : R) (h : IsOrthogonal e f) : f * (1 - e) = f := by --Maša
  calc _ = f - f * e := by noncomm_ring
      _ = f := by rw [h.2]; noncomm_ring

lemma f_mem_corner_e_e_sub_f_idem (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) (f_mem : f ∈ CornerSubring idem_e) : IsIdempotentElem (e - f) := by --Maša
  have idem_one_sub_e : IsIdempotentElem (1 - e) := by exact IsIdempotentElem.one_sub idem_e

  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f := by exact f_in_corner_othogonal (1- e) f idem_one_sub_e (by simp; exact f_mem)

  have ef_eq_f : e * f = f := by exact left_unit_mul idem_e f_mem

  unfold IsIdempotentElem
  calc _ = (e * e) - e * f + (f * f) - f * e   := by noncomm_ring
      _ = e - f + f - f * e := by rw [idem_e, ef_eq_f, idem_f]
      _ = e - f + f * (1 - e) := by noncomm_ring
      _ = e - f := by rw [one_sub_e_f_orthogonal.2]; noncomm_ring

-- lemma 2.14
theorem artinian_ring_has_minimal_left_ideal_of_element [IsArtinian R R] [Nontrivial R] : ∃ I : Ideal R, IsAtom I := by -- Maša
  exact IsAtomic.exists_atom (Ideal R)


theorem prime_and_artinian_esists_idem_corner_div [Nontrivial R] (h : IsPrimeRing R) (h' : IsArtinian R R) : -- Maša
  ∃(e : R), e ≠ 0 ∧ IsIdempotentElem e ∧ IsDivisionSubring (CornerSubringNonUnital e) e := by
  have ⟨I, hI⟩ : ∃ I : Ideal R, IsAtom I := by exact artinian_ring_has_minimal_left_ideal_of_element
  have I_sq_nonzero : I * I ≠ ⊥ := by
    specialize h I I
    by_contra I_sq_zero
    specialize h I_sq_zero
    let I_neq_zero := hI.1
    have I_eq_zero : I = ⊥ := by aesop
    contradiction
  let ⟨e, ⟨h1, h2, ⟨h3, h4, h5⟩⟩⟩ := minimal_ideal_I_sq_nonzero_exists_idem_and_div I hI I_sq_nonzero

  use e
