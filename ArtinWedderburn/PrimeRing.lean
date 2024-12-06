import ArtinWedderburn.IdealProd

variable {R : Type*} [Ring R]

-- A ring is prime if from I * J = 0 follows I = 0 or J = 0
def IsPrimeRing (R : Type*) [Ring R] : Prop := ∀ (I J : Ideal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥

-- A ring is prime if any the following equivalent statements hold
-- 1) from I * J = 0 follows I = 0 or J = 0
-- 2) for all a, b: if a R b = 0 then a = 0 or b = 0
-- 3) for all TWO-SIDED ideals I, J: I * J = 0 implies I = 0 or J = 0

-- equivalence between 1) and 2)
-- #EASIER
theorem prime_ring_equiv : IsPrimeRing R ↔ ∀ (a b : R), (a ⬝ R ⬝ b)  = ⊥ → a = 0 ∨ b = 0 := by sorry -- Matevz

-- equivalence between 1) and 3)
-- #EASIER
theorem prime_ring_equiv' : IsPrimeRing R ↔ ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by sorry -- Mikita

-- Every simple ring is prime
theorem simple_ring_is_prime [IsSimpleRing R] : IsPrimeRing R := by sorry -- Job
