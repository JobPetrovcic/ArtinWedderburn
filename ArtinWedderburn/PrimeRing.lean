import ArtinWedderburn.IdealProd
import ArtinWedderburn.SetProd

variable {R : Type*} [Ring R]

-- A ring is prime if from I * J = 0 it follows that I = 0 or J = 0 for any ideals I, J
def IsPrimeRing (R : Type*) [Ring R] : Prop := ∀ (I J : Ideal R), (I * J) = ⊥ → I = ⊥ ∨ J = ⊥

-- A ring is prime if any of the following equivalent statements hold
-- 1) from I * J = 0 follows I = 0 or J = 0
-- 2) for all a, b: if a R b = 0 then a = 0 or b = 0
-- 3) for all TWO-SIDED ideals I, J: I * J = 0 implies I = 0 or J = 0

open Pointwise Set

-- equivalence between 1) and 2)
theorem prime_ring_equiv : IsPrimeRing R ↔ ∀ (a b : R), both_mul a b = {0} → a = 0 ∨ b = 0 := by -- Done by Matevz
  constructor
  · intro hR a b hab
    have rhs : ∀ x ∈ (left_mul a) * (left_mul b), x = (0 : R) := by
      rintro x hx
      rw [both_mul_zero_one_left_zero a b hab] at hx
      trivial
    have h := hR (left_ideal_of_element a) (left_ideal_of_element b) (Ideal.span_eq_bot.mpr rhs)
    cases h with
    | inl ha =>
      apply Or.inl
      have ainbot : a ∈ left_ideal_of_element a := by use 1; simp
      rw [ha] at ainbot
      exact ainbot
    | inr hb =>
      apply Or.inr
      have binbot : b ∈ left_ideal_of_element b := by use 1; simp
      rw [hb] at binbot
      exact binbot
  · intro h I J hIJ
    have hI : I = ⊥ ∨ I ≠ ⊥ := by apply Classical.em
    cases hI with
    | inl hi => apply Or.inl; exact hi
    | inr hi =>
      apply Or.inr
      refine (Submodule.eq_bot_iff J).mpr ?mpr.inr.h.intro.intro.a
      obtain ⟨x, hx, hnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
      intro y hy
      have hxRy : both_mul x y = {0} := by
        apply Set.ext_iff.mpr
        intro z
        constructor
        · rintro ⟨r, hr⟩
          rw [hr]
          have hry : r * y ∈ J := Ideal.mul_mem_left J r hy
          have hz : x * (r * y) ∈ (↑I : Set R) * (↑J : Set R) := by
            use x
            constructor
            · trivial
            · use r * y
              constructor
              · trivial
              · simp
          have k : x*r*y = 0 := by calc
            x * r * y = x * (r * y) := by noncomm_ring
            _ = 0 := Ideal.span_eq_bot.mp hIJ (x * (r * y)) hz
          trivial
        · intro hz
          use 0
          noncomm_ring
          trivial
      cases h x y hxRy with
      | inl hx => contradiction
      | inr hy => exact hy





theorem span_le_two_sided_span (S : Set R) : Ideal.span S ≤ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := by -- Matevz
  have h : S ⊆ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := TwoSidedIdeal.subset_span
  exact Ideal.span_le.mpr h


theorem two_sided_ideal_equality (I J : TwoSidedIdeal R) : I = J ↔ (↑I : Set R) = (↑J : Set R) := by -- Matevz
  exact SetLike.ext'_iff


theorem ideal_equality (I J : Ideal R) : I = J ↔ (↑I : Set R) = (↑J : Set R) := by -- Matevz
  exact SetLike.ext'_iff


theorem equal_sets (I : TwoSidedIdeal R) : (↑(TwoSidedIdeal.asIdeal I) : Set R) = (↑I : Set R) := by rfl -- Matevz


theorem ideal_eq_to_two_sided_ideal_eq (I J : TwoSidedIdeal R) : I = J ↔ TwoSidedIdeal.asIdeal I = TwoSidedIdeal.asIdeal J := by -- Matevz
  constructor
  · intro h
    rw [h]
  · intro h
    apply (two_sided_ideal_equality I J).mpr
    rw [←equal_sets I, ←equal_sets J]
    exact (ideal_equality (TwoSidedIdeal.asIdeal I) (TwoSidedIdeal.asIdeal J)).mp h


theorem two_sided_bot_iff_set_zero (I : TwoSidedIdeal R) : I = ⊥ ↔ (I : Set R) = {0} := by -- Matevz
  exact Iff.symm (StrictMono.apply_eq_bot_iff fun ⦃a b⦄ a ↦ a)

theorem ideal_bot_iff_set_zero (I : Ideal R) : I = ⊥ ↔ (I : Set R) = {0} := by -- Matevz
  exact Iff.symm (StrictMono.apply_eq_bot_iff fun ⦃a b⦄ a ↦ a)


theorem ideal_bot (I : TwoSidedIdeal R) : I = ⊥ ↔ TwoSidedIdeal.asIdeal I = ⊥ := by -- Matevz
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply (two_sided_bot_iff_set_zero I).mpr
    apply (ideal_bot_iff_set_zero (TwoSidedIdeal.asIdeal I)).mp h

theorem ideal_span_sub_two_sided_ideal_span (S : Set R) : Ideal.span S ≤ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := by -- Matevz
  exact span_le_two_sided_span S

theorem same_prod (I J : TwoSidedIdeal R) : I * J = ⊥ → (TwoSidedIdeal.asIdeal I) * (TwoSidedIdeal.asIdeal J) = ⊥ := by -- Matevz
  intro h
  apply Ideal.ext
  intro x
  rw [Submodule.mem_bot]
  constructor
  · intro hx
    have rwhx : x ∈ Ideal.span ((I : Set R) * (J : Set R)) := hx
    have span_ineq := ideal_span_sub_two_sided_ideal_span ((I : Set R) * (J : Set R))
    apply span_ineq at rwhx
    have hxIJ : x ∈ (TwoSidedIdeal.asIdeal (I * J)) := by exact span_ineq hx
    rw [h] at hxIJ
    exact hxIJ
  · intro hx
    rw [hx]
    exact Submodule.zero_mem (TwoSidedIdeal.asIdeal I * TwoSidedIdeal.asIdeal J)



theorem prime_ring_implies_prime_by_two_sided : IsPrimeRing R → ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by -- Matevz
  rintro hR I J hIJ
  have hIJasIdeals := same_prod I J hIJ
  have h := hR (TwoSidedIdeal.asIdeal I) (TwoSidedIdeal.asIdeal J) hIJasIdeals
  cases h with
  | inl hi => apply Or.inl; exact (ideal_bot I).mpr hi
  | inr hj => apply Or.inr; exact (ideal_bot J).mpr hj



theorem two_sided_span_bot_el_zero (a : R) : TwoSidedIdeal.span {a} = ⊥ → a = 0 := by -- Matevz
  intro h
  have ha : a ∈ TwoSidedIdeal.span {a} :=
    TwoSidedIdeal.mem_span_iff.mpr fun I a_1 ↦ a_1 rfl
  rw [h] at ha
  exact ha



def mul_closure (a : R) : Set R := {x : R | ∃ y z : R, x = y * a * z} -- Job and Matevz

theorem mul_closure_left (a : R) : ∀ x y, y ∈ mul_closure a → x * y ∈ mul_closure a := by -- Job and Matevz
  rintro x y ⟨y1, y2, hy⟩
  use x * y1, y2
  simp only [mul_assoc, hy]

theorem mul_closure_right (a : R) : ∀ y x, y ∈ mul_closure a → y * x ∈ mul_closure a := by -- Job and Matevz
  rintro y x ⟨y1, y2, hy⟩
  use y1, y2 * x
  simp only [mul_assoc, hy]

theorem mul_closure_sub_span (a : R) : mul_closure a ⊆ TwoSidedIdeal.span {a} := by
  rintro x ⟨y, z, hx⟩
  rw [hx]
  have a_in_span : a ∈ TwoSidedIdeal.span {a} :=
    TwoSidedIdeal.mem_span_iff.mpr fun I a_1 ↦ a_1 rfl
  exact TwoSidedIdeal.mul_mem_right (TwoSidedIdeal.span {a}) (y * a) z (TwoSidedIdeal.mul_mem_left (TwoSidedIdeal.span {a}) y a a_in_span)



theorem ideal_mul_closure (a : R) : AddSubgroup.closure (mul_closure a) = ((TwoSidedIdeal.span (mul_closure a)) : Set R) := by -- Job and Matevz
  ext x
  have lem := @TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_absorbing R _ (mul_closure a) (mul_closure_left a) (mul_closure_right a) x
  exact id (Iff.symm lem)


theorem sub_span (s : Set R) (I : TwoSidedIdeal R) : s ⊆ I → TwoSidedIdeal.span s ≤ I := by
  intro h x hx
  exact TwoSidedIdeal.mem_span_iff.mp hx I h


theorem span_mul_closure_eq_span (a : R) : TwoSidedIdeal.span (mul_closure a) = TwoSidedIdeal.span {a} := by
  apply le_antisymm
  · apply sub_span (mul_closure a) (TwoSidedIdeal.span {a})
    exact mul_closure_sub_span a
  · apply TwoSidedIdeal.span_mono
    intro x hx
    rw [hx]
    use 1, 1
    simp

#check AddSubgroup.closure_induction

lemma both_mul_zero {a b x y: R} (hab : both_mul a b = {0}) (hx : x ∈ mul_closure a) (hy : y ∈ mul_closure b) : x * y = 0 := by
  obtain ⟨x1, x2, hx⟩ := hx
  obtain ⟨y1, y2, hy⟩ := hy
  have prod_in_both_mul : a * (x2 * y1) * b ∈ both_mul a b := by
    use x2 * y1
  have prod_zero : a * (x2 * y1) * b = 0 := by
    rw [hab] at prod_in_both_mul
    exact prod_in_both_mul
  rw [hx, hy]
  calc
    x1 * a * x2 * (y1 * b * y2) = x1 * (a * (x2 * y1) * b) * y2 := by noncomm_ring
    _ = 0 := by rw [prod_zero]; noncomm_ring

--rw [←span_mul_closure_eq_span] at hx
--  have hx' : x ∈ (TwoSidedIdeal.span (mul_closure a) : Set R) := by exact hx
--  rw [←ideal_mul_closure a] at hx'

lemma span_mul_closure_bot_forall {a b x y: R} (hab : both_mul a b = {0}) (hx : x ∈ AddSubgroup.closure (mul_closure a)) (hy : y ∈ mul_closure b ) : x * y = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz => {apply both_mul_zero hab hz hy}
  | one => { simp}
  | mul u v hu hv ihu ihv => {
    noncomm_ring
    rw [ihu, ihv]
    simp
  }
  | inv u hu ihu => {
    noncomm_ring
    rw [ihu]
    simp
  }

lemma span_mul_closure_bot_forall' {a b x y: R} (hab : both_mul a b = {0}) (hx : x ∈ TwoSidedIdeal.span {a}) (hy : y ∈ mul_closure b ) : x * y = 0 := by
  rw [←span_mul_closure_eq_span a] at hx
  apply span_mul_closure_bot_forall hab
  have hx' : x ∈ (AddSubgroup.closure (mul_closure a) : Set R) := by
    rw [ideal_mul_closure a]
    exact hx
  exact hx'
  exact hy







theorem span_mul_closure_bot (a b : R) (hab : both_mul a b = {0}) : (TwoSidedIdeal.span {a} : Set R) * (mul_closure b) = {0} := by -- Job and Matevz
  ext x
  constructor
  {
    rintro ⟨y, hy, z, hz, h⟩
    simp at h
    rw [span_mul_closure_bot_forall' hab hy hz] at h
    rw [←h]
    simp
  }
  {
    intro hx
    rw [hx]
    use 0
    constructor
    · simp
    · use 0
      constructor
      · use 0, 0
        noncomm_ring
      · simp
  }





theorem span_mul_span_bot (a b : R) (hab : both_mul a b = {0}) : (TwoSidedIdeal.span {a} : Set R) * (TwoSidedIdeal.span {b} : Set R) = {0} := by -- Job and Matevz
  sorry


theorem bothmul_zero_implies_prod_zero (a b : R) : both_mul a b = {0} → TwoSidedIdeal.span {a} * TwoSidedIdeal.span {b} = ⊥ := by -- Job and Matevz
  intro hab
  have k : TwoSidedIdeal.span ({0} : Set R) = ⊥ := Eq.symm (TwoSidedIdealProd.ideal_eq_span ⊥)
  rw [TwoSidedIdealProd.mul_two_sided_ideal_eq_span]
  unfold TwoSidedIdealProd.ring_subset_prod_two_sided_ideal
  rw [←k]
  rw [span_mul_span_bot a b hab]


theorem prime_for_two_sided_implies_condition2 : (∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥) → (∀ (a b : R), both_mul a b = {0} → a = 0 ∨ b = 0) := by -- Matevz
  rintro hR a b hab
  have RaRbR_zero : TwoSidedIdeal.span {a} * TwoSidedIdeal.span {b} = ⊥ := bothmul_zero_implies_prod_zero a b hab
  have h := hR (TwoSidedIdeal.span {a}) (TwoSidedIdeal.span {b}) RaRbR_zero
  cases h with
  | inl ha =>
    apply Or.inl
    exact two_sided_span_bot_el_zero a ha
  | inr hb =>
    apply Or.inr
    exact two_sided_span_bot_el_zero b hb




-- equivalence between 1) and 3)
theorem prime_ring_equiv' : IsPrimeRing R ↔ ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by -- Matevz
  constructor
  · exact prime_ring_implies_prime_by_two_sided
  · intro hR
    exact prime_ring_equiv.mpr (prime_for_two_sided_implies_condition2 hR)





-- Every simple ring is prime
theorem simple_ring_is_prime [IsSimpleRing R] : IsPrimeRing R := by -- Done by Matevz
  apply prime_ring_equiv'.mpr
  intro I J hIJ
  cases eq_bot_or_eq_top I with
    | inl hi => apply Or.inl; exact hi
    | inr hi =>
      apply Or.inr
      cases eq_bot_or_eq_top J with
      | inl hj => exact hj
      | inr hj =>
        have h : I * J = ⊤ := by
          apply (TwoSidedIdeal.one_mem_iff (I * J)).mp
          apply TwoSidedIdeal.subset_span
          use 1
          constructor
          · rw [hi]; trivial
          · use 1
            constructor
            · rw [hj]; trivial
            · simp
        rw [hIJ] at h
        have k : (⊥ : TwoSidedIdeal R) ≠ (⊤ : TwoSidedIdeal R) := by exact bot_ne_top
        absurd h
        trivial
