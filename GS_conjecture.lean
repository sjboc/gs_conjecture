import Mathlib.Tactic
import Mathlib.Init.Function
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Rat.Cast
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.MvPolynomial.Basic

open MvPolynomial

universe u v

def FinProduct (R : Type u) [CommSemiring R] : (n : ℕ) → (Fin n → R) → R := fun
  | .zero => λ _ => 1
  | .succ n => λ f => (f 0) * (FinProduct R n (λ x => f (Fin.succ x))) 

-- checking the above definition by implementing the factorial function
-- #eval FinProduct ℚ 5 (λ k => 1 + (Fin.valEmbedding k : ℚ))

def FinSum (R : Type u) [CommSemiring R] : (n : ℕ) → (Fin n → R) → R := fun
  | .zero => λ _ => 0
  | .succ n => λ f => (f 0) + (FinSum R n (λ x => f (Fin.succ x))) 

-- -- checking the above definition by implementing the n*(n + 1)/2 function
-- #eval FinSum ℚ 5 (λk => 1 + (Fin.valEmbedding k : ℚ))


lemma FinProductZero {R : Type u} [CommSemiring R] {f : Fin 0 → R} 
  : FinProduct R 0 f = 1 := by
  constructor

lemma FinProductSucc {R : Type u} [CommSemiring R] {n : ℕ} {f : Fin (n + 1) → R} 
  : FinProduct R (n + 1) f = (f 0) * (FinProduct R n (λ x => f (Fin.succ x))) := by
  constructor

lemma FinSumZero {R : Type u} [CommSemiring R] {f : Fin 0 → R} 
  : FinSum R 0 f = 0 := by
  constructor

lemma FinSumSucc {R : Type u} [CommSemiring R] {n : ℕ} {f : Fin (n + 1) → R} 
  : FinSum R (n + 1) f = (f 0) + (FinSum R n (λ x => f (Fin.succ x))) := by
  constructor


lemma FinProduct_eq_Zero {R : Type u} [CommSemiring R] [NoZeroDivisors R] {n : ℕ} 
  {f : Fin n → R} {k : Fin n} {hk : f k = 0} : (FinProduct R n f) = 0 := by
    induction n with
    | zero => exact Fin.elim0 k
    | succ n hn =>  cases' k with k hk' 
                    rw[FinProductSucc]
                    rw[mul_eq_zero]
                    cases k with
                    | zero => left
                              exact hk
                    | succ k => right
                                rw[@hn _ ⟨k, Nat.lt_of_succ_lt_succ hk'⟩]
                                rw[Fin.succ_mk]
                                exact hk

lemma FinProduct_eq_One {R : Type u} [CommSemiring R] {n : ℕ} 
  {f : Fin n → R} {hf : ∀ (k : Fin n), f k = 1} : (FinProduct R n f) = 1 := by
    induction n with
    | zero => exact FinProductZero
    | succ n hn => rw[FinProductSucc]
                   rw[hf 0]
                   rw[one_mul]
                   rw[hn]
                   intro k
                   exact hf (Fin.succ k)

lemma FinSum_eq_Zero {R : Type u} [CommSemiring R] {n : ℕ} 
  {f : Fin n → R} {hf : ∀ (k : Fin n), f k = 0} : (FinSum R n f) = 0 := by
    induction n with
    | zero => exact FinSumZero
    | succ n hn => rw[FinSumSucc]
                   rw[hf 0]
                   rw[zero_add]
                   rw[hn]
                   intro k
                   exact hf (Fin.succ k)

lemma FinSum_almost_all_Zero {R : Type u} [CommSemiring R] {n : ℕ} {f : Fin n → R}
  {k : Fin n} {hk : ∀ (t : Fin n), (t ≠ k) → f t = 0} : (FinSum R n f) = f k := by
    induction n with
    | zero => exact Fin.elim0 k
    | succ n hn => rw[FinSumSucc]
                   cases' k with k hk'
                   cases k with
                   | zero => rw[FinSum_eq_Zero]
                             rw[add_zero, Fin.mk_zero]
                             intro t
                             rw[hk]
                             rw[Fin.mk_zero]
                             exact Fin.succ_ne_zero t
                   | succ k => rw[@hn _ ⟨k, Nat.lt_of_succ_lt_succ hk'⟩]
                               rw[Fin.succ_mk]
                               rw[hk]
                               rw[zero_add]
                               intro q
                               apply Fin.succ_ne_zero ⟨k, Nat.lt_of_succ_lt_succ hk'⟩
                               exact q.symm
                               intro t ht
                               apply hk
                               rw[← Fin.succ_mk]
                               intro ht'
                               rw[Fin.succ_inj] at ht'
                               exact ht ht' 


lemma EvalFinProduct_eq_FinProductEval {R : Type u} [CommSemiring R] 
  {m n : ℕ} {f : Fin n → MvPolynomial (Fin m) R} {g : Fin m → R} :
  eval g (FinProduct (MvPolynomial (Fin m) R) n f)
  = FinProduct R n ((eval g) ∘ f) := by
    induction n with
    | zero => repeat rw[FinProductZero]
              rw[map_one]
    | succ n hn => repeat rw[FinProductSucc]
                   rw[map_mul]
                   rw[Function.comp_apply]
                   rw[hn]
                   rfl

lemma MapFinProduct_eq_FinProductMap {R : Type u} [CommSemiring R] {S : Type v} 
  [CommSemiring S] {m n : ℕ} {f : Fin n → MvPolynomial (Fin m) R} {g : R →+* S} :
  map g (FinProduct (MvPolynomial (Fin m) R) n f)
  = FinProduct (MvPolynomial (Fin m) S) n ((map g) ∘ f) := by 
    induction n with
    | zero => repeat rw[FinProductZero]
              rw[map_one]
    | succ n hn => repeat rw[FinProductSucc]
                   rw[map_mul]
                   rw[Function.comp_apply]
                   rw[hn]
                   rfl

lemma EvalFinSum_eq_FinSumEval {R : Type u} [CommSemiring R] 
  {m n : ℕ} {f : Fin n → MvPolynomial (Fin m) R} {g : Fin m → R} :
  eval g (FinSum (MvPolynomial (Fin m) R) n f)
  = FinSum R n ((eval g) ∘ f) := by
    induction n with
    | zero => repeat rw[FinSumZero]
              rw[map_zero]
    | succ n hn => repeat rw[FinSumSucc]
                   rw[map_add]
                   rw[Function.comp_apply]
                   rw[hn]
                   rfl

lemma MapFinSum_eq_FinSumMap {R : Type u} [CommSemiring R] {S : Type v} 
  [CommSemiring S] {m n : ℕ} {f : Fin n → MvPolynomial (Fin m) R} {g : R →+* S} :
  map g (FinSum (MvPolynomial (Fin m) R) n f)
  = FinSum (MvPolynomial (Fin m) S) n ((map g) ∘ f) := by 
    induction n with
    | zero => repeat rw[FinSumZero]
              rw[map_zero]
    | succ n hn => repeat rw[FinSumSucc]
                   rw[map_add]
                   rw[Function.comp_apply]
                   rw[hn]
                   rfl


noncomputable section

def LBF_f_x_y (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (f : Fin n → Fin m) (x : Fin n) (y : Fin m)
  : MvPolynomial (Fin n) R := by
    by_cases ((f x) = y)
    exact MvPolynomial.C 1
    exact (Z (f x) - Z y)⁻¹ • ((MvPolynomial.X x) + (MvPolynomial.C (-(Z y))))

def LBF_f_x (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (f : Fin n → Fin m) (x : Fin n)
  : MvPolynomial (Fin n) R := 
    FinProduct (MvPolynomial (Fin n) R) m (λ y => LBF_f_x_y R n m Z f x y)

def LBF_f (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (f : Fin n → Fin m)
  : MvPolynomial (Fin n) R := 
    FinProduct (MvPolynomial (Fin n) R) n (λ x => LBF_f_x R n m Z f x)

def Fin_fun_to_pow {n m : ℕ} (f : Fin n → Fin m) : Fin (n^m) := sorry

def Fin_pow_to_fun {n m : ℕ} (k : Fin (n^m)) : (Fin n → Fin m) := sorry

lemma Fin_pow_fun_inv {n m : ℕ} : (@Fin_pow_to_fun n m) ∘ (@Fin_fun_to_pow n m) = id := sorry

lemma Fin_inv_fun_pow {n m : ℕ} : (@Fin_fun_to_pow n m) ∘ (@Fin_pow_to_fun n m) = id := sorry
            

def Lagrange_Interpolation (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (V : (Fin n → Fin m) → R)
  : MvPolynomial (Fin n) R := 
    FinSum (MvPolynomial (Fin n) R) (n^m) 
      (λ k => (V (Fin_pow_to_fun k)) • LBF_f R n m Z V (Fin_pow_to_fun k))

lemma LBF_f_x_y_eq_One {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R} {hZ : Function.Injective Z}
  {f : Fin n → Fin m} {x : Fin n} {y : Fin m}
  {g : Fin n → R} {hg : (g x) = Z (f x)} 
  : ((MvPolynomial.eval g (LBF_f_x_y R n m Z f x y)) = 1) := by
    unfold LBF_f_x_y
    by_cases (f x = y)
    simp only [dite_eq_ite, h, ite_true]
    repeat rw [map_one]
    simp only [dite_eq_ite, h, ite_false]
    simp only [map_add, smul_eval, eval_X, eval_C, mul_neg]
    rw [hg]
    rw[← sub_eq_add_neg]
    have q : Z (f x) - Z y ≠ 0 := by
      intro p
      have p' : Z (f x) - Z y + Z y = Z y := by
        simp only [p, zero_add]
      simp only [sub_add_cancel] at p' 
      exact ((h (hZ p')))
    simp only [ne_eq, q, not_false_eq_true, inv_mul_cancel]

lemma LBF_f_x_eq_One (R : Type u) [Field R] [DecidableEq R] (n m : ℕ)
  (Z : Fin m → R) (hZ : Function.Injective Z)
  (f : Fin n → Fin m) (x : Fin n) (y : Fin m)
  (g : Fin n → R) (hg : (g x) = Z (f x)) 
  : ((MvPolynomial.eval g (LBF_f_x R n m Z f x)) = 1) := by
    unfold LBF_f_x
    rw [EvalFinProduct_eq_FinProductEval]
    apply FinProduct_eq_One
    intro k
    simp only [Function.comp_apply]
    exact @LBF_f_x_y_eq_One _ _ _ _ _ _ hZ _ _ _ _ hg
    
-- lemma LBF_f_eq_One TODO


/-

send 0 1 to 2
send 0 0 to 3

2 * (1 * 1 * (X_2 - 0) 1) + 3 * (1 * 1 * (X_2 - 1) 1)

-/



