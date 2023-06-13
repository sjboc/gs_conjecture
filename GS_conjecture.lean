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
  {f : Fin n → R} (k : Fin n) (hk : f k = 0) : (FinProduct R n f) = 0 := by
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
  (k : Fin n) (hk : ∀ (t : Fin n), (t ≠ k) → f t = 0) : (FinSum R n f) = f k := by
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
    exact C 1
    exact (Z (f x) - Z y)⁻¹ • ((X x) + (C (-(Z y))))

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

lemma Fin_pow_fun_inv {n m : ℕ} : ∀ k, (@Fin_pow_to_fun n m) ((@Fin_fun_to_pow n m) k) = k := sorry

lemma Fin_fun_pow_inv {n m : ℕ} : ∀ k, (@Fin_fun_to_pow n m) ((@Fin_pow_to_fun n m) k) = k := sorry
            

def Lagrange_Interpolation (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (V : (Fin n → Fin m) → R)
  : MvPolynomial (Fin n) R := 
    FinSum (MvPolynomial (Fin n) R) (n^m) 
      (λ k => (V (Fin_pow_to_fun k)) • LBF_f R n m Z (Fin_pow_to_fun k))

lemma LBF_f_x_y_eq_One {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R} (hZ : Function.Injective Z)
  {f : Fin n → Fin m} {x : Fin n} {y : Fin m}
  {g : Fin n → R} (hg : (g x) = Z (f x)) 
  : ((eval g (LBF_f_x_y R n m Z f x y)) = 1) := by
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

lemma LBF_f_x_eq_One {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R} (hZ : Function.Injective Z)
  {f : Fin n → Fin m} {x : Fin n}
  {g : Fin n → R} (hg : (g x) = Z (f x)) 
  : ((eval g (LBF_f_x R n m Z f x)) = 1) := by
    unfold LBF_f_x
    rw [EvalFinProduct_eq_FinProductEval]
    apply FinProduct_eq_One
    intro k
    rw [Function.comp_apply]
    exact LBF_f_x_y_eq_One hZ hg
    
lemma LBF_f_eq_One {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R} (hZ : Function.Injective Z)
  {f : Fin n → Fin m}
  {g : Fin n → R} (hg : (k : Fin n) → (g k) = Z (f k)) 
  : ((eval g (LBF_f R n m Z f)) = 1) := by
    unfold LBF_f
    rw [EvalFinProduct_eq_FinProductEval]
    apply FinProduct_eq_One
    intro k
    rw [Function.comp_apply]
    exact LBF_f_x_eq_One hZ (hg k)

lemma LBF_f_x_eq_Zero {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R}
  {f : Fin n → Fin m} {x : Fin n}
  {g : Fin n → R} {w : Fin m} 
  (hg : (g x) = (Z w)) (hw : (f x) ≠ w)
  : ((eval g (LBF_f_x R n m Z f x)) = 0) := by
    unfold LBF_f_x 
    rw [EvalFinProduct_eq_FinProductEval]
    apply FinProduct_eq_Zero w
    rw [Function.comp_apply]
    unfold LBF_f_x_y 
    simp only [dite_eq_ite, hw, map_one, ite_false]
    simp only [map_add, smul_eval, eval_X, eval_C]
    rw [mul_eq_zero]
    right
    rw [hg]
    simp only [add_right_neg]

lemma LBF_f_eq_Zero {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R}
  {f : Fin n → Fin m}
  {g : Fin n → R} (h : Fin n → Fin m) 
  (hg : ∀ (k : Fin n), (g k) = Z (h k)) (hh : ∃ (k : Fin n), f k ≠ h k)
  : ((eval g (LBF_f R n m Z f)) = 0) := by
    unfold LBF_f
    rw [EvalFinProduct_eq_FinProductEval]
    rcases hh with ⟨k, hk⟩
    apply FinProduct_eq_Zero k
    rw [Function.comp_apply]
    exact LBF_f_x_eq_Zero (hg k) hk

theorem Eval_Lagrange_Interpolation {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R} (hZ : Function.Injective Z) {V : (Fin n → Fin m) → R}
  {g : Fin n → Fin m}
  : (eval (Z ∘ g) (Lagrange_Interpolation R n m Z V) = V g) := by
    unfold Lagrange_Interpolation
    rw [EvalFinSum_eq_FinSumEval]
    have q : V g = (eval (Z ∘ g) ∘ (λ k => 
      V (Fin_pow_to_fun k) • LBF_f R n m Z (Fin_pow_to_fun k))) (Fin_fun_to_pow g) := by
        rw [Function.comp_apply]
        rw [Fin_pow_fun_inv]
        simp only [smul_eval]
        have q' : (eval (Z ∘ g) (LBF_f R n m Z g)) = 1 := by
          apply LBF_f_eq_One hZ
          intro k
          exact Function.comp_apply
        rw [q']
        rw [mul_one]
    rw [q]
    apply FinSum_almost_all_Zero
    intros t ht
    rw [Function.comp_apply]
    simp only [smul_eval, mul_eq_zero]
    right
    apply LBF_f_eq_Zero g
    intro k
    rw [Function.comp_apply]
    have ht' : Fin_pow_to_fun t ≠ g := by
      intro p
      have p' : Fin_fun_to_pow (Fin_pow_to_fun t) = Fin_fun_to_pow g := by
        simp only [p]
      rw [Fin_fun_pow_inv] at p'
      exact ht p'
    have ht'' : ¬ (∀ k, (Fin_pow_to_fun t) k = g k) := by
      exact λ p => ht' (funext p)
    rw [not_forall] at ht'' 
    simp only [ne_eq]
    exact ht''

lemma LBF_f_x_fx_deg_x {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R}
  {f : Fin n → Fin m} {x : Fin n}
  : ((degreeOf x (LBF_f_x_y R n m Z f x (f x))) = 0) := by
    unfold LBF_f_x_y
    simp only [dite_eq_ite, ite_true]
    rw [degreeOf_C]

lemma LBF_f_x_y_deg_x {R : Type u} [Field R] [DecidableEq R] {n m : ℕ}
  {Z : Fin m → R}
  {f : Fin n → Fin m} {x : Fin n} {y : Fin m}
  (hf : f x ≠ y)
  : ((degreeOf x (LBF_f_x_y R n m Z f x y)) ≤ 1) := by
    sorry
    -- unfold LBF_f_x_y
    -- simp only [hf, dite_eq_ite, ite_false]
    -- rw [← le_zero_iff]
    -- rw [smul_eq_C_mul]
    -- have q : (degreeOf x (C (Z (f x) - Z y)⁻¹)) + (degreeOf x ((X x) + C (- Z y))) = 0 := by
    --   rw [degreeOf_C]
    --   rw [zero_add]
    --   rw [← le_zero_iff]
    --   have q' : (degreeOf x (X x)) + (degreeOf x (C (-Z y))) = 0 := by
    --     rw [degreeOf_X]
    -- rw [← q]
    -- exact degreeOf_mul_le x (C (Z (f x) - Z y)⁻¹) ((X x) + C (- Z y))


