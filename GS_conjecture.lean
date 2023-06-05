import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Cast

open MvPolynomial

universe u

def FinProduct (R : Type u) [Field R] : (n : ℕ) → (Fin n → R) → R := fun
  | .zero => λ _ => 1
  | .succ n => λ f => (f 0) * (FinProduct R n (f ∘ Fin.succ)) 

-- checking the above definition by implementing the factorial
-- #eval FinProduct ℚ 5 (λ k => 1 + (Fin.valEmbedding k : ℚ))

lemma FinProductZero (R : Type u) [Field R] : (n : ℕ) → (f : Fin n → R)
  → (k : Fin n) → (f k = 0) → (FinProduct R n f) = 0 := by
    intro n
    induction n with
    | zero => rintro _ ⟨k, hk'⟩
              exact (Nat.not_lt_zero _ hk').elim
    | succ n hn =>  rintro f ⟨k, hk'⟩ hk 
                    unfold FinProduct
                    rw[mul_eq_zero]
                    cases k with
                    | zero => left
                              exact hk
                    | succ k => right
                                apply hn (f ∘ Fin.succ) 
                                  ⟨k, Nat.lt_of_succ_lt_succ hk'⟩
                                rw[Function.comp_apply, Fin.succ_mk]
                                exact hk

