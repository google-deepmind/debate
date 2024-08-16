import Prob.Bernoulli
import Prob.Estimate
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Weak Chernoff bound for {0,1} variables

We prove Hoeffding's inequality just for the Bernoulli case
1. https://en.m.wikipedia.org/wiki/Hoeffding%27s_inequality
2. https://en.m.wikipedia.org/wiki/Hoeffding%27s_lemma
-/

open Prob
open Real (log)
open Set

lemma exp_bernoulli_exp {p : ℝ} (m : p ∈ Icc 0 1) (t : ℝ) :
    (bernoulli p).exp (λ x ↦ (t * bif x then 1 else 0).exp) = 1 - p + p * t.exp := by
  simp only [exp_bernoulli _ m, cond_false, mul_zero, Real.exp_zero, mul_one, cond_true]

lemma uniqueDiffWithinAt_Icc {a b t : ℝ} (ab : a < b) (m : t ∈ Icc a b) :
    UniqueDiffWithinAt ℝ (Icc a b) t := by
  apply uniqueDiffWithinAt_convex (convex_Icc _ _)
  simp only [interior_Icc]; exact nonempty_Ioo.mpr ab; simp only [closure_Icc, m]

/-- Get rid of Within from iteratedDeriv for smooth functions -/
lemma iteratedDerivWithin_eq_iteratedDeriv {f : ℝ → ℝ} (fc : ContDiff ℝ ⊤ f)
    {a b t : ℝ} (ab : a < b) (m : t ∈ Icc a b) {n : ℕ} :
    iteratedDerivWithin n f (Icc a b) t = iteratedDeriv n f t := by
  induction' n with n h generalizing m t
  · simp only [Nat.zero_eq, ge_iff_le, not_le, gt_iff_lt, iteratedDerivWithin_zero,
      iteratedDeriv_zero]
  · have u : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffWithinAt_Icc ab m
    rw [iteratedDerivWithin_succ u, iteratedDeriv_succ, ←derivWithin_univ,
      ←derivWithin_subset (subset_univ _) u]
    apply derivWithin_congr; exact λ _ m ↦ h m; exact h m
    apply DifferentiableAt.differentiableWithinAt
    apply fc.differentiable_iteratedDeriv
    apply WithTop.coe_lt_top

/-- The L function used in the Hoeffding's lemma proof -/
noncomputable def L (p : ℝ) (t : ℝ) := log (1 - p + p * t.exp)

-- Properties of L.  For some reason putting this inside hoeffdings_lemma causes a pile of errors
variable {p t : ℝ}
lemma L_pos (m : p ∈ Icc 0 1) : 0 < 1 - p + p * t.exp := by
  by_cases p0 : p = 0; simp only [p0, sub_zero, zero_mul, add_zero, zero_lt_one]
  apply add_pos_of_nonneg_of_pos; linarith [m.2]
  apply mul_pos; exact (Ne.symm p0).lt_of_le m.1; apply Real.exp_pos
lemma Lc (m : p ∈ Icc 0 1) : ContDiff ℝ ⊤ (L p) := by
  apply ContDiff.log; exact contDiff_const.add (contDiff_const.mul Real.contDiff_exp)
  intro t; exact ne_of_gt (L_pos m)
lemma L_0 : L p 0 = 0 := by simp only [L, Real.exp_zero, mul_one, sub_add_cancel, Real.log_one]
lemma L_d0 : HasDerivAt (λ t ↦ p * t.exp) (p * t.exp) t := (Real.hasDerivAt_exp _).const_mul _
lemma L_d1 : HasDerivAt (λ t ↦ 1 - p + p * t.exp) (p * t.exp) t := L_d0.const_add _
lemma dL (m : p ∈ Icc 0 1) : HasDerivAt (L p) (p * t.exp / (1 - p + p * t.exp)) t :=
  L_d1.log (ne_of_gt (L_pos m))
lemma ddL (m : p ∈ Icc 0 1) :
    HasDerivAt (λ t ↦ deriv (L p) t) ((p * t.exp * (1 - p:)) / (1 - p + p * t.exp)^2) t := by
  have h : HasDerivAt (λ t ↦ deriv (L p) t)
      ((p * t.exp * ((1 - p:) + p * t.exp) -
        p * t.exp * (p * t.exp)) / ((1 - p:) + p * t.exp)^2) t := by
    simp only [(dL m).deriv]; exact L_d0.div L_d1 (ne_of_gt (L_pos m))
  simp only [←mul_sub, add_sub_assoc, sub_self, add_zero] at h; exact h
lemma L_taylor (m : p ∈ Icc 0 1) (t0 : 0 < t) :
    ∃ a ∈ Ioo 0 t, L p t = p * a.exp * (1 - p:) / (1 - p + p * a.exp)^2 * t^2 / 2 + t * p := by
  have Lc1 : ContDiffOn ℝ ↑1 (L p) (Icc 0 t) := ((Lc m).of_le le_top).contDiffOn
  have d2 : DifferentiableOn ℝ (iteratedDerivWithin 1 (L p) (Icc 0 t)) (Ioo 0 t) :=
    ((Lc m).contDiffOn.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_top 1)
      (uniqueDiffOn_Icc t0)).mono Ioo_subset_Icc_self
  rcases @taylor_mean_remainder_lagrange (L p) t 0 1 t0 Lc1 d2 with ⟨a,am,h⟩
  simp only [ge_iff_le, not_le, gt_iff_lt, taylorWithinEval_succ, taylor_within_zero_eval,
    Real.exp_zero, mul_one, sub_add_cancel, Real.log_one, CharP.cast_eq_zero, zero_add,
    Nat.factorial, Nat.cast_one, inv_one, sub_zero, pow_one, one_mul, smul_eq_mul, Nat.mul_one,
    Nat.cast_succ, iteratedDeriv_one, iteratedDeriv_zero, iteratedDeriv_succ, div_one,
    iteratedDerivWithin_eq_iteratedDeriv (Lc m) t0 (left_mem_Icc.mpr (le_of_lt t0)),
    iteratedDerivWithin_eq_iteratedDeriv (Lc m) t0 (Ioo_subset_Icc_self am),
    (dL m).deriv, (ddL m).deriv,
    sub_eq_iff_eq_add, L_0] at h
  simp only [L_0, one_add_one_eq_two, L] at h
  use a, am, h

/-- Special case of AMGM, expressed as a bound on the ratio -/
lemma mul_div_sq_sum_le {x y : ℝ} (x0 : 0 ≤ x) (y0 : 0 ≤ y) : x * y / (x + y)^2 ≤ 1/4 := by
  by_cases s0 : x + y = 0; simp only [s0, zero_pow]; norm_num
  replace s0 : 0 < x + y := (Ne.symm s0).lt_of_le (add_nonneg x0 y0)
  rw [div_le_iff (pow_pos s0 2), one_div, mul_comm 4⁻¹, ←div_eq_mul_inv]
  have h : (0:ℝ) ≤ (x - y)^2 := sq_nonneg _
  simp only [pow_two, mul_add, add_mul] at h ⊢
  linarith

/-- The Beroulli case of Hoeffding's lemma -/
lemma hoeffdings_lemma {p : ℝ} (m : p ∈ Icc 0 1) {t : ℝ} (t0 : 0 ≤ t) :
    (bernoulli p).exp (λ x ↦ (t * bif x then 1 else 0).exp) ≤ (t*p + t^2/8).exp := by
  simp only [exp_bernoulli_exp m]
  have p1 : 0 ≤ 1-p := by linarith [m.2]
  by_cases tz : t = 0
  · simp [tz]
  replace t0 := (Ne.symm tz).lt_of_le t0; clear tz
  rw [←Real.exp_log (L_pos m), Real.exp_le_exp]
  rcases L_taylor m t0 with ⟨a,_,h⟩
  simp only [L] at h; rw [h]; clear h; norm_num
  generalize hb : p * a.exp = b
  have b0 : 0 ≤ b := by rw [←hb]; exact mul_nonneg m.1 (Real.exp_nonneg _)
  have amgm : (1-p:) * b / (1 - p + b)^2 ≤ 1/4 := mul_div_sq_sum_le p1 b0
  simp only [mul_comm b _, ←mul_div _ _ (2 : ℝ)] at amgm ⊢
  apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right amgm _) _)
  swap; apply div_nonneg (pow_nonneg (le_of_lt t0) _) (by norm_num)
  have e : (1:ℝ)/(4:ℝ) * (t^2 / (2:ℝ)) = t^2 / 8 := by ring
  simp only [e, add_comm (t*p) _]; rfl

/-- The Bool case of Hoeffding's lemma -/
lemma hoeffdings_lemma' (f : Prob Bool) {t : ℝ} (t0 : 0 ≤ t) :
    f.exp (λ x ↦ (t * bif x then 1 else 0).exp) ≤ (t * f.prob true + t^2/8).exp := by
  have m := f.prob_mem_Icc true; rw [f.eq_bernoulli]
  simp only [bernoulli_prob_true m]; exact hoeffdings_lemma m t0

/-- Moment generating function for count -/
lemma exp_count (f : Prob Bool) (n : ℕ) (t : ℝ) :
    (count f n).exp (λ x ↦ (t*x).exp) = (f.exp (λ x ↦ (t * bif x then 1 else 0).exp)) ^ n := by
  induction' n with k h
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, zero_mul, Real.exp_zero, count, exp_pure, pow_zero,
      mul_zero]
  · generalize hz : f.exp (λ x ↦ (t * bif x then 1 else 0).exp) = z
    simp only [hz] at h
    have i : ∀ x, ↑(bif x then (1 : ℕ) else (0 : ℕ)) = (bif x then (1 : ℝ) else (0 : ℝ)) := by
      intro x; induction x; repeat simp only [cond_false, cond_true, Nat.cast_one, Nat.cast_zero]
    simp only [count, Nat.cast_succ, add_mul, one_mul, Real.exp_add, exp_bind, exp_pure,
      Nat.cast_add, exp_const_mul, exp_mul_const, h, hz, mul_comm _ z.exp, i, pow_succ, mul_ite,
      mul_add, mul_one, mul_zero]
    ring

/-- Weak Chernoff's theorem for the Bernoulli case -/
lemma chernoff_count_le (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
    (count f n).pr (λ x ↦ n * f.prob true + t ≤ x) ≤ (-2 * t^2 / n).exp := by
  generalize hp : f.prob true = p
  by_cases tz : t = 0
  · simp only [tz, pow_two, mul_zero, zero_div, Real.exp_zero, zero_pow]; apply pr_le_one
  replace t0 := (Ne.symm tz).lt_of_le t0; clear tz
  by_cases nz : n = 0
  · simp only [nz, count, Nat.cast_zero, zero_mul, zero_add, pr, exp_pure, div_zero, Real.exp_zero]
    split; rfl; norm_num
  have h : ∀ s, 0 < s → (count f n).pr (λ x ↦ n * p + t ≤ x) ≤ (-s*t + n * s^2 / 8).exp := by
    intros s s0
    simp only [←@mul_le_mul_left _ _ (_ * _ + _) _ _ _ _ _ _ s0, ←@Real.exp_le_exp (_ * _) _]
    apply le_trans (markov' _ _ (λ _ _ ↦ le_of_lt (Real.exp_pos _)) (Real.exp_pos _))
    simp only [exp_count]
    have le := hoeffdings_lemma' f (le_of_lt s0)
    generalize hz : f.exp (λ x ↦ (s * bif x then 1 else 0).exp) = z; simp only [hz] at le ⊢
    have z0 : 0 ≤ z := by rw [←hz]; apply exp_nonneg; intro x _; apply Real.exp_nonneg
    rw [div_le_iff (Real.exp_pos _), ←Real.exp_add]
    apply le_trans (pow_le_pow_left z0 le n); clear le z0 hz z
    simp only [hp, ←Real.rpow_natCast, ←Real.exp_mul]
    simp only [Real.rpow_natCast, Real.exp_le_exp, mul_comm _ (n:ℝ), mul_add, mul_div, ←add_assoc,
      ←mul_assoc]
    simp only [add_comm _ (s*t), ←add_assoc]; simp only [neg_mul, add_right_neg, zero_add]
    simp only [add_comm (_ / _)]; apply add_le_add_right; rfl
  apply le_trans (h (4*t/n) (by positivity)); simp only [Real.exp_le_exp]; apply le_of_eq
  simp only [Nat.cast_ofNat, Nat.cast_pow, neg_mul, div_pow, mul_pow, ←mul_assoc, mul_div, pow_two,
    div_eq_mul_inv, mul_inv, Nat.cast_mul, mul_pow, pow_two]
  ring_nf
  rw [pow_two (n:ℝ)⁻¹, ←mul_assoc, mul_assoc _ (n:ℝ), mul_inv_cancel (Nat.cast_ne_zero.mpr nz),
    mul_one]
  ring

/-- Chernoff lower bound -/
lemma chernoff_le_count (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
    (count f n).pr (λ x ↦ x ≤ n * f.prob true - t) ≤ (-2 * t^2 / n).exp := by
  have h := chernoff_count_le (not <$> f) n t0
  simp only [count_not, pr_map] at h
  have e : ∀ k, (count f n).prob k ≠ 0 →
      (↑n * (not <$> f).prob true + t ≤ ↑(n - k) ↔ ↑k ≤ ↑n * f.prob true - t) := by
    intro k m
    simp only [not_bool_prob, Bool.not_true, bool_prob_false_of_true, Nat.cast_sub (count_le' _ m),
      mul_sub, mul_one, sub_add, sub_le_sub_iff_left]
  rw [pr_congr e] at h; exact h

/-- Chernoff symmetric bound -/
lemma chernoff_count_abs_le (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
    (count f n).pr (λ x ↦ t ≤ |x - n * f.prob true|) ≤ (2:ℝ) * ((-2:ℝ) * t^2 / n).exp := by
  simp only [le_abs, two_mul]; apply le_trans (pr_or_le _ _); apply add_le_add
  · simp only [le_sub_iff_add_le, add_comm t _]; exact chernoff_count_le _ _ t0
  · simp only [neg_sub, @le_sub_iff_add_le _ _ _ _ _ ((_ : ℕ) : ℝ), add_comm t _,
      ←@le_sub_iff_add_le _ _ _ _ _ t]
    exact chernoff_le_count _ _ t0

/-- Chernoff symmetric bound for estimate -/
lemma chernoff_estimate_abs_le (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
    (estimate f n).pr (λ x ↦ t ≤ |x - f.prob true|) ≤ (2:ℝ) * ((-2:ℝ) * n * t^2).exp := by
  by_cases n0 : (n : ℝ) = 0
  · simp only [n0, mul_zero, zero_mul, Real.exp_zero]
    exact le_trans pr_le_one (by norm_num)
  have np : 0 < (n : ℝ) := (Ne.symm n0).lt_of_le (Nat.cast_nonneg _)
  simp only [estimate, pr_map]
  have b := chernoff_count_abs_le f n (mul_nonneg (Nat.cast_nonneg n) t0)
  simp only [mul_pow, div_eq_inv_mul, ←mul_assoc, pow_two (n:ℝ)] at b
  rw [mul_comm _ (n:ℝ)] at b; simp only [←mul_assoc, mul_inv_cancel n0, one_mul] at b
  apply le_trans _ b; apply le_of_eq
  apply pr_congr; intro x _; simp only [mul_comm _ t, ←le_div_iff np]
  nth_rewrite 3 [←abs_of_pos np]; simp only [←abs_div, sub_div]; field_simp [n0]
