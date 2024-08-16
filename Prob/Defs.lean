import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Finsupp.Basic
import Misc.Finset

/-!
Finitely supported probability distributions as a monad

This is the finitely supported case of Pmf.  I wrote my own instead of Pmf because I wasn't
familiar with Lean probability theory, and didn't realize Pmf existed: I thought I'd have to
use general measures, and this would require a lot measurability and integrability side
conditions.  However, I think Pmf still would have integrability side conditions when
expectations are involved, so I'm going to stick with my finitely supported version for now.

Prob/Pmf.lean shows that Prob injects into Pmf, which is evidence these definitions are correct.
-/

open Classical
open Set
open scoped Real
noncomputable section

variable {α β γ : Type}

/-- Prob α is a finitely supported probability distribution over results α -/
structure Prob (α : Type) where
  /-- Finitely supported probabilities -/
  prob : α →₀ ℝ
  /-- prob is nonnegative -/
  prob_nonneg : ∀ {x}, 0 ≤ prob x
  /-- The total probability is 1 -/
  total : prob.sum (λ _ p ↦ p) = 1

/-- The support for f -/
def Prob.supp (f : Prob α) : Finset α := f.prob.support

/-- Integral w.r.t. a distribution -/
def Prob.exp (f : Prob α) (g : α → ℝ) : ℝ :=
  f.prob.sum (λ x p ↦ p * g x)

/-- Expectation of a real-valued distribution -/
def Prob.mean (f : Prob ℝ) : ℝ := f.exp id

/-- The probability that a prop holds -/
def Prob.pr (f : Prob α) (p : α → Prop) :=
  f.exp (λ x ↦ if p x then 1 else 0)

/-- Conditional probabilities: f.cond p q = Pr_f(p | q) = f.pr (p ∧ q) / f.pr q -/
def Prob.cond (f : Prob α) (p q : α → Prop) : ℝ :=
  f.pr (λ x ↦ p x ∧ q x) / f.pr q

/-- Conditional expectations: f.cexp u q = E_f(u | q) = f.exp (u * q) / f.pr q -/
def Prob.cexp (f : Prob α) (u : α → ℝ) (q : α → Prop) : ℝ :=
  f.exp (λ x ↦ if q x then u x else 0) / f.pr q

namespace Prob

-- Basics
lemma zero_iff {f : Prob α} {x : α} : f.prob x = 0 ↔ x ∉ f.supp := Finsupp.not_mem_support_iff.symm
lemma zero (f : Prob α) {x : α} (m : x ∉ f.supp) : f.prob x = 0 := Finsupp.not_mem_support_iff.mp m
lemma mem_iff {f : Prob α} {x : α} : x ∈ f.supp ↔ f.prob x ≠ 0 := Finsupp.mem_support_iff
lemma mem_iff_pos {f : Prob α} {x : α} : x ∈ f.supp ↔ 0 < f.prob x := by
  rw [f.mem_iff]; constructor; intro e; exact e.symm.lt_of_le f.prob_nonneg; exact ne_of_gt

/-- Probs are equal if their probabilities are -/
@[ext] lemma ext {f g : Prob α} (h : ∀ x, f.prob x = g.prob x) : f = g := by
  induction' f with p _ _; induction' g with q _ _; simp only [mk.injEq]; ext x; apply h

/-- Probs are equal iff their probabilities are -/
lemma ext_iff {f g : Prob α} : f = g ↔ ∀ x, f.prob x = g.prob x := by
  constructor; intro e x; simp only [e]; intro h; exact Prob.ext h

/-- Prob is a monad -/
instance : Monad Prob where
  pure := λ x ↦ {
    prob := Finsupp.single x 1
    prob_nonneg := by intro x; simp only [Finsupp.single_apply]; split; norm_num; norm_num
    total := Finsupp.sum_single_index rfl
  }
  bind := λ f g ↦ by
    set prob := f.prob.sum (λ x p ↦ p • (g x).prob)
    have nonneg : ∀ x, 0 ≤ prob x := by
      intro _; simp only [Finsupp.sum_apply, prob]; apply Finset.sum_nonneg
      intro _ _; exact mul_nonneg f.prob_nonneg (g _).prob_nonneg
    have total : prob.sum (λ _ p ↦ p) = 1 := by
      rw [Finsupp.sum_sum_index]
      · have e : ∀ (p : ℝ) x, (p • (g x).prob).sum (λ _ q ↦ q) = p := by
          intro p x; rw [Finsupp.sum_smul_index, ←Finsupp.mul_sum, Prob.total, mul_one]
          simp only [implies_true]
        simp only [e, Prob.total]
      · simp only [implies_true]
      · simp only [forall_const, implies_true]
    exact { prob := prob, prob_nonneg := fun {_} => nonneg _, total := total }

end Prob
