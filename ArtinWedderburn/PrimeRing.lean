import ArtinWedderburn.IdealProd
import ArtinWedderburn.SetProd

variable {R : Type*} [Ring R]

-- A ring is prime if from I * J = 0 it follows that I = 0 or J = 0 for any ideals I, J
def IsPrimeRing (R : Type*) [Ring R] : Prop := ∀ (I J : Ideal R), (I * J) = ⊥ → I = ⊥ ∨ J = ⊥

-- A ring is prime if any the following equivalent statements hold
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
    have h := hR (left_ideal a) (left_ideal b) (Ideal.span_eq_bot.mpr rhs)
    cases h with
    | inl ha =>
      apply Or.inl
      have ainbot : a ∈ left_ideal a := by use 1; simp
      rw [ha] at ainbot
      exact ainbot
    | inr hb =>
      apply Or.inr
      have binbot : b ∈ left_ideal b := by use 1; simp
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



-- equivalence between 1) and 3)
-- #EASIER
theorem prime_ring_equiv' : IsPrimeRing R ↔ ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by sorry -- Mikita





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
