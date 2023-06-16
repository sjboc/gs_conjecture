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


lemma FinProduct_mul {R : Type u} [CommSemiring R] {n : ℕ} {f g : Fin n → R} :
  (FinProduct R n f) * (FinProduct R n g) = FinProduct R n (λ k => (f k) * (g k)) := by
    induction n with
    | zero => repeat rw [FinProductZero]
              exact mul_one _
    | succ n hn => {
      repeat rw [FinProductSucc]
      rw [← mul_assoc]
      simp only [mul_comm]
      rw [← mul_assoc]
      simp only [mul_comm]
      rw [← hn]
      rw [mul_assoc]
    } 

lemma FinSum_add {R : Type u} [CommSemiring R] {n : ℕ} {f g : Fin n → R} :
  (FinSum R n f) + (FinSum R n g) = FinSum R n (λ k => (f k) + (g k)) := by
    induction n with
    | zero => repeat rw [FinSumZero]
              exact add_zero _
    | succ n hn => {
      repeat rw [FinSumSucc]
      rw [← add_assoc]
      simp only [add_comm]
      rw [← add_assoc]
      simp only [add_comm]
      rw [← hn]
      rw [add_assoc]
    } 

lemma FinSum_mul {R : Type u} [CommSemiring R] {n : ℕ} {f : Fin n → R} {r : R} :
  r * FinSum R n f = FinSum R n (λ k => r * (f k)) := by
    induction n with
    | zero => simp only [Nat.zero_eq, FinSumZero, mul_zero]
    | succ n hn =>  simp only [FinSumSucc] 
                    rw [mul_add, hn]

lemma FinSum_sub {R : Type u} [CommRing R] {n : ℕ} {f g : Fin n → R} :
  (FinSum R n f) - (FinSum R n g) = FinSum R n (λ k => (f k) - (g k)) := by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, FinSum_mul, FinSum_add]
    simp only [neg_mul, one_mul]
    simp only [sub_eq_add_neg]

lemma FinSum_Ones {R : Type u} [CommSemiring R] {n : ℕ} :
  (FinSum R n (λ _ => 1)) = n := by
    induction n with
    | zero => simp only [Nat.zero_eq, FinSumZero, Nat.cast_zero]
    | succ n hn =>  simp only [FinSumSucc, Nat.cast_succ]
                    rw [hn]
                    rw [add_comm]


lemma FinSum_Nat_le {n : ℕ} {f g : Fin n → ℕ} 
  {hf : ∀ k, 0 < (f k)} {p : ∀ k, (f k) ≤ (g k)} :
  (FinSum ℕ n f) ≤ (FinSum ℕ n g) := by 
    induction n with
    | zero => repeat rw [FinSumZero]
    | succ n hn =>  repeat rw [FinSumSucc]
                    have q := @hn (λ x => f (Fin.succ x)) (λ x => g (Fin.succ x)) 
                      (λ x => hf (Fin.succ x)) (λ x => p (Fin.succ x))
                    exact calc (f 0) + FinSum ℕ n (λ x => f (Fin.succ x))
                      ≤ (f 0) + FinSum ℕ n (λ x => g (Fin.succ x)) := by {
                        apply add_le_add_left
                        exact q
                      }
                      _ ≤ (g 0) + FinSum ℕ n (λ x => g (Fin.succ x)) := by {
                        apply add_le_add_right
                        exact p 0
                      }


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


def Fin_fun_to_pow : (n m : ℕ) → (Fin n → Fin m) → Fin (m^n) :=
  fun
  | .zero => λ _ _ => ⟨0, by 
    rw [Nat.zero_eq, pow_zero]
    exact Nat.zero_lt_one⟩ 
  | .succ n =>  fun
    | .zero => λ f => f 0
    | .succ m => λ f => ⟨(f 0).1 + (m + 1) * (Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1, by
      exact calc  (f 0).1 + (m + 1) * (Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1 
                  = (f 0).1 + (m + 1) * ((Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1 + 1 - 1) := by 
                    simp only [add_tsub_cancel_right]
                  _ < (m + 1) + (m + 1) * ((Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1 + 1 - 1) := by
                    simp only [add_lt_add_iff_right, (f 0).2]
                  _ = (m + 1) + (m + 1) * 
                  ((Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1 + 1) - (m + 1) := by
                    rw [Nat.mul_sub_left_distrib]
                    simp only [mul_one, add_pos_iff, or_true, 
                      le_mul_iff_one_le_right, le_add_iff_nonneg_left, 
                      zero_le, add_tsub_cancel_of_le, add_tsub_cancel_left]
                  _ = (m + 1) * ((Fin_fun_to_pow _ _ (f ∘ Fin.succ)).1 + 1) := by
                    simp only [add_tsub_cancel_left]
                  _ ≤ (m + 1) * ((m + 1) ^ n) := by
                    simp only [gt_iff_lt, add_pos_iff, or_true, mul_le_mul_left]
                    rw [← Nat.lt_iff_add_one_le]
                    exact (Fin_fun_to_pow _ _ (f ∘ Fin.succ)).2
                  _ = (m + 1) ^ (n + 1) := by
                    rw [Nat.pow_succ']⟩

-- def bool_test : Fin 2 → Fin 3 := by
--   rintro ⟨y, _⟩
--   cases y with
--   | zero => exact 2
--   | succ _ => exact 1

-- #eval Fin_fun_to_pow _ _ bool_test
                            
def Fin_pow_to_fun : (m n : ℕ) → Fin (m^n) → (Fin n → Fin m) :=
  fun
  | .zero =>  fun
              | .zero => λ _ x => x 
              | .succ _ => λ x _ => x
  | .succ m => λ _ k ⟨a, _⟩ => ⟨(k / ((m + 1)^a)) % (m + 1), 
                    Nat.mod_lt _ (gt_iff_lt.mp (Nat.zero_lt_succ _))⟩

-- def y := 5

-- #eval (Fin_pow_to_fun 3 2 y) 0
-- #eval (Fin_pow_to_fun 3 2 y) 1


-- Please ignore how bad these proofs are
lemma Fin_pow_fun_inv : {n m : ℕ} → ∀ k, (Fin_pow_to_fun m n) ((Fin_fun_to_pow n m) k) = k := by
  intro n
  induction n with
  | zero => intros m k
            unfold Fin_pow_to_fun
            simp only [Nat.zero_eq, eq_iff_true_of_subsingleton]
  | succ n hn =>  intros m k
                  cases m with
    | zero => simp only [Nat.zero_eq, eq_iff_true_of_subsingleton]
    | succ m => {
      apply funext
      rintro ⟨x, hx⟩
      rw [Fin.mk_eq_mk]
      unfold Fin_fun_to_pow
      unfold Fin_pow_to_fun
      simp only
      rw [Nat.add_div_eq_of_add_mod_lt]
      {
      cases x with
      | zero => simp only [Nat.zero_eq, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, 
        Fin.mk_zero, Nat.mod_succ_eq_iff_lt, Fin.is_lt]
      | succ x => {
        exact calc ((k 0).1 / (m + 1) ^ (x + 1) + (m + 1) * ↑(Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ)) / (m + 1) ^ (x + 1)) % (m + 1) 
          = ((m + 1) * (Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ))/(m + 1)^(x + 1)) % (m + 1) := by {
              have q : (k 0).1 / (m + 1) ^ (x + 1) + (m + 1) * ↑(Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ)) / (m + 1)^(x + 1) 
              = ((m + 1) * (Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ))/(m + 1)^(x + 1)) := by
                simp only [add_left_eq_self]
                apply Nat.div_eq_zero
                exact calc  (k 0).1 < m + 1 := (k 0).2
                    _ ≤ (m + 1) * (m + 1)^x := by
                      simp only [add_pos_iff, or_true,
                      le_mul_iff_one_le_right, 
                      Nat.one_le_pow']
                    _ = (m + 1)^(x + 1) := by 
                      simp only [Nat.pow_succ']
              rw [q]
            }
          _ = (m + 1) * (Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ))/((m + 1) * (m + 1)^x) % (m + 1) := by
              simp only [Nat.pow_succ']
          _ = (Fin_fun_to_pow n (m + 1) (k ∘ Fin.succ))/((m + 1)^x) % (m + 1) := by
                simp only [add_pos_iff, or_true, Nat.mul_div_mul_left]
          _ = ((k ∘ Fin.succ) ⟨x, Nat.lt_of_succ_lt_succ hx⟩).1 := by
              have q : (Fin_pow_to_fun _ _ (Fin_fun_to_pow _ _ (k ∘ Fin.succ))) ⟨x, Nat.lt_of_succ_lt_succ hx⟩ 
                = (k ∘ Fin.succ) ⟨x, Nat.lt_of_succ_lt_succ hx⟩ := by
                simp only [hn, Function.comp_apply, Fin.succ_mk]
              unfold Fin_pow_to_fun at q
              simp only at q
              rw [Fin.mk_eq_mk] at q
              rw [q]
          _ = (k ⟨x + 1, hx⟩).1 := by
              simp only [Function.comp_apply, Fin.succ_mk]
        }
      }
      cases x with
      | zero => simp only [Nat.zero_eq, pow_zero, Nat.lt_one_iff, add_eq_zero, Nat.mod_one]
      | succ x => { 
        exact calc  (k 0).1 % (m + 1)^(x + 1) + (m + 1) * (Fin_fun_to_pow _ _ (k ∘ Fin.succ)).1 % (m + 1)^(x + 1) 
          = (k 0).1 + (m + 1) * (Fin_fun_to_pow _ _ (k ∘ Fin.succ)).1 % (m + 1)^(x + 1) := by {
            simp only [add_left_inj]
            rw [Nat.mod_eq_iff_lt]
            exact calc  (k 0).1 < (m + 1) := (k 0).2
                        _ ≤ (m + 1)^(x + 1) := by
                          simp only [ne_eq, add_eq_zero, and_false, Nat.le_self_pow]
            simp only [ne_eq, add_pos_iff, or_true, pow_eq_zero_iff, add_eq_zero, and_false, not_false_eq_true]
          }
          _ = (k 0).1 + (m + 1) * (Fin_fun_to_pow _ _ (k ∘ Fin.succ)).1 % ((m + 1) * (m + 1)^x) := by {
            simp only [Nat.pow_succ']
          }
          _ = (k 0).1 + (m + 1) * ((Fin_fun_to_pow _ _ (k ∘ Fin.succ)).1 % ((m + 1)^x)) := by {
            simp only [add_lt_add_iff_left, Nat.mul_mod_mul_left]
          }
          _ ≤ (k 0).1 + (m + 1) * ((m + 1)^x - 1) := by {
            simp only [ge_iff_le, add_le_add_iff_left, gt_iff_lt, add_pos_iff, or_true, mul_le_mul_left]
            rw [← Nat.lt_succ_iff, Nat.sub_one, Nat.succ_pred]
            simp only [gt_iff_lt, add_pos_iff, or_true, pow_pos, Nat.mod_lt]
            apply ne_of_gt
            simp only [gt_iff_lt, add_pos_iff, or_true, pow_pos]
          }
          _ = (k 0).1 + ((m + 1) * (m + 1)^x - (m + 1)) := by
            simp only [ge_iff_le, Nat.mul_sub_left_distrib, mul_one, gt_iff_lt, add_pos_iff, or_true,
              mul_le_iff_le_one_right]
          _ < (m + 1) + ((m + 1) * (m + 1)^x - (m + 1)) := by
            simp only [ge_iff_le, gt_iff_lt, add_pos_iff, or_true, mul_le_iff_le_one_right, le_mul_iff_one_le_right,
              add_lt_add_iff_right, Fin.is_lt]
          _ = (m + 1) + (m + 1) * (m + 1)^x - (m + 1) := by
            rw [Nat.add_sub_assoc]
            simp only [gt_iff_lt, add_pos_iff, or_true, le_mul_iff_one_le_right, Nat.one_le_pow]
          _ = (m + 1)^(x + 1) := by
            simp only [ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero, add_eq_zero, and_false,
              false_or, add_tsub_cancel_left, Nat.pow_succ']
          }
      }                              

lemma Fin_fun_pow_inv : {n m : ℕ} → ∀ k, (@Fin_fun_to_pow n m) ((@Fin_pow_to_fun m n) k) = k := by
  intro n
  induction n with
  | zero => intros m k
            simp at k
            simp only [Nat.zero_eq, Nat.pow_zero, eq_iff_true_of_subsingleton]
  | succ n hn => {
    intro m
    cases m with
    | zero => intro k
              unfold Fin_pow_to_fun
              unfold Fin_fun_to_pow
              simp only
    | succ m => intro k
                unfold Fin_pow_to_fun
                unfold Fin_fun_to_pow
                simp only [Fin.ofNat'_zero, Fin.val_zero, pow_zero, Nat.div_one]
                rw [Fin.mk_eq_mk]
                cases' k with k hk 
                {
    cases k with
    | zero => simp only [Nat.zero_eq, Nat.zero_mod, Nat.zero_div, Fin.mk_zero, zero_add, mul_eq_zero, add_eq_zero,
      and_false, false_or]
              have q := @hn (m + 1) 0
              unfold Fin_pow_to_fun at q
              simp only [Nat.add_eq, Fin.val_zero, add_zero, Nat.zero_div, Nat.zero_mod, Fin.mk_zero] at q 
              rw [Fin.mk_eq_mk] at q
              exact calc (Fin_fun_to_pow n (Nat.succ m) ((λ _ => 0) ∘ Fin.succ)).1
                          = (Fin_fun_to_pow n (Nat.succ m) (λ _ => 0)).1 := by 
                            have p : ((λ _ => 0) ∘ Fin.succ) = (λ (_ : Fin n) => (0 : Fin (m + 1))) := by
                              apply funext
                              intro _
                              simp only [Function.comp_apply]
                            rw [p]
                          _ = 0 := by
                            simp only [q, Fin.val_zero]
    | succ k => simp only
                let k' := (k + 1)/(m + 1)
                have hk' : (k' < ((m + 1)^n)) := by
                  exact calc (k + 1)/(m + 1) < (m + 1)^(n + 1)/(m + 1) := by {
                    apply Nat.div_lt_div_of_lt_of_dvd
                    use (m + 1)^n
                    exact Nat.pow_succ'
                    exact hk
                  }
                  _ = ((m + 1)^n * (m + 1))/(m + 1) := by {
                    simp only [Nat.pow_succ]
                  }
                  _ = (m + 1)^n := by {
                    simp only [add_pos_iff, or_true, Nat.mul_div_left]
                  }
                have q := (@hn (m + 1)) ⟨k', hk'⟩
                unfold Fin_pow_to_fun at q
                simp only [Nat.add_eq, add_zero] at q 
                rw [Fin.mk_eq_mk] at q
                have q' : (λ (x : Fin n) =>
      (({ val := (k + 1) / (m + 1) / (m + 1) ^ x.1 % (m + 1), isLt := (by {
          apply Nat.mod_lt
          simp only [gt_iff_lt, add_pos_iff, or_true]
          } : (k + 1) / (m + 1) / (m + 1) ^ x.1 % (m + 1) < m + 1) }) : Fin (m + 1)))
                  = ((λ (x : Fin (n + 1)) =>
              ({ val := (k + 1) / (m + 1) ^ x.1 % (m + 1), isLt := (by {
                apply Nat.mod_lt
                simp only [gt_iff_lt, add_pos_iff, or_true]
                } : (k + 1) / (m + 1) ^ x.1 % (m + 1) < m + 1) } : Fin (m + 1))) ∘ Fin.succ) := by {
                apply funext
                rintro ⟨x, hx⟩
                simp only [Function.comp_apply, Fin.succ_mk, Fin.mk.injEq]
                have q'' : (k + 1)/(m + 1) / (m + 1)^x = (k + 1) / (m + 1)^(x + 1) := by {
                  rw [Nat.div_div_eq_div_mul, Nat.pow_succ']
                }
                rw [q'']
              }
                simp only [Nat.add_eq, q'] at q 
                simp only [q]
                exact Nat.mod_add_div _ _
      }
  } 


def Lagrange_Interpolation (R : Type u) [Field R] [DecidableEq R] (n m : ℕ) 
  (Z : Fin m → R) (V : (Fin n → Fin m) → R)
  : MvPolynomial (Fin n) R := 
    FinSum (MvPolynomial (Fin n) R) (m^n) 
      (λ k => (V (Fin_pow_to_fun _ _ k)) • LBF_f R n m Z (Fin_pow_to_fun _ _ k))

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
  {g : Fin n → R} (hg : ∀ k, (g k) = Z (f k)) 
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
      V (Fin_pow_to_fun _ _ k) • LBF_f R n m Z (Fin_pow_to_fun _ _ k))) (Fin_fun_to_pow _ _ g) := by
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
    have ht' : Fin_pow_to_fun _ _ t ≠ g := by
      intro p
      have p' : Fin_fun_to_pow _ _ (Fin_pow_to_fun _ _ t) = Fin_fun_to_pow _ _ g := by
        simp only [p]
      rw [Fin_fun_pow_inv] at p'
      exact ht p'
    have ht'' : ¬ (∀ k, (Fin_pow_to_fun _ _ t) k = g k) := by
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

lemma LBF_f_x_y_deg_x {R : Type u} [Field R] [DecidableEq R] [Nontrivial R] {n m : ℕ}
  {Z : Fin m → R}
  {f : Fin n → Fin m} {x : Fin n} {y : Fin m}
  (hf : f x ≠ y)
  : ((degreeOf x (LBF_f_x_y R n m Z f x y)) ≤ 1) := by
    unfold LBF_f_x_y
    simp only [hf, dite_eq_ite, ite_false, smul_eq_C_mul]
    exact calc  degreeOf x (C (Z (f x) - Z y)⁻¹ * (X x + C (-Z y)))
                ≤ degreeOf x (C (Z (f x) - Z y)⁻¹) + degreeOf x (X x + C (-Z y)) := by {
                  exact degreeOf_mul_le _ _ _ 
                }
                _ = degreeOf x (X x + C (-Z y)) := by {
                  simp only [degreeOf_C, zero_add]
                }
                _ ≤ max (degreeOf x (X x)) (degreeOf x (C (-Z y))) := by {
                  exact degreeOf_add_le _ _ _
                }
                _ ≤ 1 := by {
                  simp only [degreeOf_X,  degreeOf_C,max_eq_left]
                }

