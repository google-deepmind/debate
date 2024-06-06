import Prob.Arith

/-!
Estimate the probability of a Prob Bool by sampling
-/

open Classical
open Prob
open Set
open scoped Real
noncomputable section

-- We allow an arbitrary monad to support both `Prob` and `Comp s`
universe u
variable {m : Type → Type u} [Monad m]

/-- `count f n` is the distribution of the number of `true` of `f` after `n` samples. -/
def count (f : m Bool) : ℕ → m ℕ
| 0 => pure 0
| n+1 => do
  let x := bif ←f then 1 else 0
  let y ← count f n
  return x + y

-- Facts about count
@[simp] lemma count_zero (f : m Bool) : count f 0 = pure 0 := by simp only [count]
lemma count_le (f : Prob Bool) {n k : ℕ} : n < k → (count f n).prob k = 0 := by
  induction' n with n lo generalizing k
  · intro h; simp only [count, prob_pure, Nat.le_zero] at h ⊢
    by_cases k0 : k = 0
    · simp only [k0, lt_self_iff_false] at h
    · simp only [k0, ↓reduceIte, one_ne_zero]
  · intro h; simp only [count, prob_bind, prob_pure] at h ⊢
    apply Finset.sum_eq_zero; intro x _; rw [mul_eq_zero]; right
    apply Finset.sum_eq_zero; intro l m; induction x
    · simp only [cond_false, zero_add, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
      intro e; apply lo; rw [←e]; refine lt_trans (Nat.lt_succ.mpr ?_) h; rfl
    · simp only [Finsupp.mem_support_iff] at m
      simp only [cond_true, mul_eq_zero, m, false_or]
      contrapose m; simp only [not_not]; apply lo
      by_cases kl : k = 1 + l
      · rw [kl, add_comm 1 _, Nat.succ_lt_succ_iff] at h; exact h
      · simp only [kl, ↓reduceIte, not_true_eq_false] at m
lemma count_le' (f : Prob Bool) {n k : ℕ} : (count f n).prob k ≠ 0 → k ≤ n := by
  intro h; contrapose h; simp only [not_le, not_not] at h ⊢; exact count_le _ h

/-- Estimate a probability via sample mean -/
def estimate (f : m Bool) (n : ℕ) : m ℝ := (λ x : ℕ ↦ (x : ℝ) / n) <$> count f n

/-- count.mean = n * f.prob true -/
lemma mean_count (f : Prob Bool) (n : ℕ) : (count f n).exp (λ x ↦ ↑x) = n * f.prob true := by
  induction' n with k h
  · simp only [count, mean, pure_bind, exp_pure, id, Nat.cast_zero, zero_mul]
  · simp only [count, exp_bind, exp_pure, Nat.cast_add, exp_add, exp_const, h, exp_bool, cond_false,
      Nat.cast_zero, mul_zero, cond_true, Nat.cast_succ, zero_add, mul_one]; ring

/-- count of the negative of f -/
lemma count_not (f : Prob Bool) (n : ℕ) : (count (not <$> f) n) = (λ x ↦ n - x) <$> count f n := by
  induction' n with k h
  · simp only [Nat.zero_eq, ge_iff_le, zero_le, tsub_eq_zero_of_le, Prob.map_const, count_zero]
  · simp only [count, h, seq_bind_eq, Function.comp, map_bind, map_pure]
    apply Prob.bind_congr; intro x _; apply Prob.bind_congr; intro n m; induction x
    · simp only [Bool.not_false, cond_true, cond_false, zero_add]
      by_cases nk : n ≤ k
      · simp only [Bool.not_false, cond_true, ge_iff_le, cond_false, zero_add, ←Nat.add_sub_assoc nk,
          Nat.add_comm 1 k]
      · contrapose m; clear m; simp only [not_le, not_not] at nk ⊢; exact count_le f nk
    · simp only [Bool.not_true, cond_false, ge_iff_le, zero_add, cond_true, add_comm 1 n,
        Nat.succ_sub_succ_eq_sub]

/-- estimate.mean = f.prob true -/
lemma mean_estimate (f : Prob Bool) {n : ℕ} (n0 : n ≠ 0) : (estimate f n).mean = f.prob true := by
  simp only [mean, estimate, exp_map, id, exp_div, mean_count, Function.comp]
  field_simp [n0]
