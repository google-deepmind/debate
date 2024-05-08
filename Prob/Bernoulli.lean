import Prob.Arith
import Mathlib.Data.Finsupp.Notation

/-!
Bernoulli distributions
-/

open Classical
open Prob
open Set
open scoped Real
noncomputable section

/-- Bernoulli random variable.
    We clamp probabilities to [0,1] so that any probability can be passed in. -/
def bernoulli (p' : ℝ) : Prob Bool := by
  set p := max 0 (min 1 p')
  exact {
    prob := fun₀ | true => p | false => 1-p
    prob_nonneg := by
      intro x; induction x
      · simp only [ge_iff_le, min_le_iff, le_min_iff, zero_le_one, true_and, Finsupp.coe_update,
          Function.update_same, sub_nonneg, max_le_iff, le_refl, true_or, and_self, p]
      · simp (config := {decide := true}) only [ge_iff_le, min_le_iff, le_min_iff, zero_le_one, true_and, Finsupp.coe_update, ne_eq,
          Function.update_noteq, Finsupp.single_eq_same, le_max_iff, le_refl, true_or, p]
    total := by
      simp (config := {decide := true}) only [Finsupp.sum_fintype, Fintype.sum_bool, ge_iff_le, min_le_iff, le_min_iff, zero_le_one,
        true_and, Finsupp.coe_update, ne_eq, Function.update_noteq, Finsupp.single_eq_same,
        Function.update_same, add_sub_cancel]
  }

-- If p is arbitrary, the probabilities are clamped
lemma bernoulli_prob_true' (p : ℝ) : (bernoulli p).prob true = max 0 (min 1 p) := by
  simp (config := {decide := true}) only [prob, bernoulli, ge_iff_le, min_le_iff, le_min_iff, zero_le_one, true_and, Finsupp.coe_update,
    ne_eq, Function.update_noteq, Finsupp.single_eq_same]
lemma bernoulli_prob_false' (p : ℝ) : (bernoulli p).prob false = 1 - max 0 (min 1 p) := by
  simp only [bool_prob_false_of_true, bernoulli_prob_true']

-- If p is in [0,1], the probabilities are as expected
lemma bernoulli_prob_true {p : ℝ} (m : p ∈ Icc 0 1) : (bernoulli p).prob true = p := by
  simp only [bernoulli_prob_true', ite_true, min_eq_right m.2, max_eq_right m.1]
lemma bernoulli_prob_false {p : ℝ} (m : p ∈ Icc 0 1) : (bernoulli p).prob false = 1-p := by
  simp only [bool_prob_false_of_true, bernoulli_prob_true m]

/-- 1/2 ∈ [0,1] -/
lemma half_mem_Icc : (1/2 : ℝ) ∈ Icc 0 1 := by norm_num

/-- One random bit -/
def bit : Prob Bool := bernoulli (1/2)
lemma bit_prob (x : Bool) : bit.prob x = 1/2 := by
  induction x
  · have h := bernoulli_prob_false half_mem_Icc
    norm_num at h; exact h
  · exact bernoulli_prob_true half_mem_Icc

/-- The expectation of a Bernoulli distribution in terms of true and false values -/
lemma exp_bernoulli (p : ℝ) (m : p ∈ Icc 0 1) (f : Bool → ℝ) : (bernoulli p).exp f = (1-p) * f false + p * f true := by
  simp only [exp_bool, bernoulli_prob_false m, bernoulli_prob_true m]

/-- All Bool computations are Bernoulli -/
lemma Prob.eq_bernoulli (f : Prob Bool) : f = bernoulli (f.prob true) := by
  ext x; induction x
  · simp only [bernoulli_prob_true (f.prob_mem_Icc _), bool_prob_false_of_true]
  · simp only [bernoulli_prob_true (f.prob_mem_Icc _)]
