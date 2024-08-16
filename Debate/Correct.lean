import Debate.Details
import Debate.Protocol

/-!
Correctness of the stochastic oracle doubly-efficient debate algorithm
-/

open Classical
open Prob
open scoped Real
noncomputable section

variable {t : ℕ} {k : ℝ}

/-- Completeness for any valid parameters -/
theorem completeness (o : Oracle) (L : o.lipschitz t k) (eve : Bob)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob true) :
    d ≤ ((debate (alice p.c p.q) eve (vera p.c p.s p.v) t).prob' o).prob true :=
  completeness_p o L eve p m

/-- Soundness for any valid parameters -/
theorem soundness (o : Oracle) (L : o.lipschitz t k) (eve : Alice)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob false) :
    d ≤ ((debate eve (bob p.s p.b p.q) (vera p.c p.s p.v) t).prob' o).prob false :=
  soundness_p o L eve p m

/-- Default valid parameters (not tuned) -/
def defaults (k : ℝ) (t : ℕ) (k0 : 0 < k) : Params (2/3) (3/5) k t where
  v := 1/100
  c := 1/(100*k)
  s := 2/(100*k)
  b := 5/(100*k)
  q := 1/(100*(t+1))
  k0 := k0
  cs := by rw [div_lt_div_right]; norm_num; positivity
  sb := by rw [div_lt_div_right]; norm_num; positivity
  q1 := by
    rw [div_le_one]; apply one_le_mul_of_one_le_of_one_le (by norm_num)
    simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]; positivity
  v1 := by norm_num
  qv := by
    rw [←div_div]; apply div_le_self (by norm_num)
    simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
  bw := by
    simp only [div_eq_mul_inv, mul_inv, ←mul_assoc, mul_comm _ k⁻¹, inv_mul_cancel (ne_of_gt k0)]
    norm_num
  complete := by
    simp only [←mul_div_assoc, mul_one, mul_comm _ k, ←div_div, div_self (ne_of_gt k0)]
    rw [mul_comm_div, div_self (Nat.cast_add_one_ne_zero t)]; norm_num
  sound := by
    simp only [←mul_div_assoc, mul_one, mul_comm _ k, ←div_div, div_self (ne_of_gt k0)]
    rw [mul_comm k 5, mul_div_assoc, div_self (ne_of_gt k0), mul_comm_div,
      div_self (Nat.cast_add_one_ne_zero t)]
    norm_num

/-- The debate protocol is correct with probability 3/5, using the default parameters -/
theorem correctness (k : ℝ) (k0 : 0 < k) (t : ℕ) :
    let p := defaults k t k0
    Correct (3/5) k t (alice p.c p.q) (bob p.s p.b p.q) (vera p.c p.s p.v) where
  half_lt_w := by norm_num
  complete o eve L m := completeness o L eve (defaults k t k0) m
  sound o eve L m := soundness o L eve (defaults k t k0) m
