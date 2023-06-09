import Mathlib.Algebra.MonoidAlgebra.Basic

universe u v

def FinMvPolynomial (R : Type u) (n : ℕ) [CommSemiring R] :=
  AddMonoidAlgebra R (Fin n → ℕ)

namespace FinMvPolynomial

instance decidableEqFinMvPolynomial {R : Type u} (n : ℕ)
  [CommSemiring R] [DecidableEq R] :
    DecidableEq (FinMvPolynomial R n) := Finsupp.decidableEq

-- instance nonUnitalCommSemiring {R : Type u} {n : ℕ} 
--   [CommSemiring R] [hn : CommSemigroup (Fin n → ℕ)] :
--     NonUnitalCommSemiring (MonoidAlgebra R (Fin n → ℕ)) :=
--   { MonoidAlgebra.nonUnitalSemiring with
--     mul_comm := fun f g => by
--       simp only [MonoidAlgebra.mul_def, Finsupp.sum]
--       rw [Finset.sum_comm]
--       simp only [CommSemigroup.mul_comm]
--       have q : 

--   }
      -- simp only [mul_def, Finsupp.sum, mul_comm]
      -- rw [Finset.sum_comm]
      -- simp only [mul_comm] }

-- instance commSemiring [CommSemiring R] : 
--   CommSemiring (FinMvPolynomial n R) := 
--     { AddMonoidAlgebra.nonUnitalCommSemiring, AddMonoidAlgebra.semiring with }













-- import Mathlib.Data.Finsupp.Defs
-- import Mathlib.LinearAlgebra.Pi
-- import Mathlib.LinearAlgebra.Span

-- open Set LinearMap Submodule
-- open Classical BigOperators

-- variable {α : Type _} {M : Type _} {N : Type _} {P : Type _} {R : Type _} {S : Type _}
-- variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
-- variable [AddCommMonoid N] [Module R N]
-- variable [AddCommMonoid P] [Module R P]




-- def single (a : α) (b : M) : α →₀ M
--     where
--   support :=
--     haveI := Classical.decEq M
--     if b = 0 then ∅ else {a}
--   toFun :=
--     haveI := Classical.decEq α
--     Pi.single a b
--   mem_support_toFun a' := by
--     classical
--       obtain rfl | hb := eq_or_ne b 0
--       · simp [Pi.single, update]
--       rw [if_neg hb, mem_singleton]
--       obtain rfl | ha := eq_or_ne a' a
--       · simp [hb, Pi.single, update]
--       simp [Pi.single_eq_of_ne' ha.symm, ha]

-- def singleAddHom (a : α) : M →+ α →₀ M where
--   toFun := single a
--   map_zero' := Finsupp.single_zero a
--   map_add' := Finsupp.single_add a

-- /-- Interpret `Finsupp.single a` as a linear map. -/
-- def lsingle (a : α) : M →ₗ[R] α →₀ M :=
--   { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

