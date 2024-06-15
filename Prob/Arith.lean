import Prob.Basics
import Misc.If

/-!
Arithmetic on Prob
-/

open Classical
open Set
open scoped Real
noncomputable section

variable {α β : Type}

namespace Prob

-- Arithmetic
instance : Zero (Prob ℝ) where zero := return 0
instance : One (Prob ℝ) where one := return 1
instance : Neg (Prob ℝ) where neg f := return -(←f)
instance : Add (Prob ℝ) where add f g := return (←f) + (←g)
instance : Mul (Prob ℝ) where mul f g := return (←f) * (←g)
instance : SMul ℝ (Prob ℝ) where smul s f := return s * (←f)

-- Arithmetic definitions expanded
lemma zero_eq : (0 : Prob ℝ) = pure 0 := rfl
lemma one_eq : (1 : Prob ℝ) = pure 1 := rfl
lemma neg_eq (f : Prob ℝ) : -f = do let x ← f; return -x := rfl
lemma add_eq (f g : Prob ℝ) : f + g = do let x ← f; let y ← g; return x + y := rfl
lemma mul_eq (f g : Prob ℝ) : f * g = do let x ← f; let y ← g; return x * y := rfl
lemma smul_eq (s : ℝ) (f : Prob ℝ) : s • f = do let x ← f; return s * x := rfl

/-- Prob is a commutative monoid (not a group since x - x ≠ 0) -/
instance : AddCommMonoid (Prob ℝ) where
  add_assoc x y z := by simp only [add_eq, bind_assoc, pure_bind, add_assoc]
  zero_add x := by simp only [add_eq, zero_eq, pure_bind, zero_add, bind_pure]
  add_zero x := by simp only [add_eq, zero_eq, pure_bind, add_zero, bind_pure]
  add_comm x y := by simp only [add_eq]; rw [bind_comm_of_eq]; ext x y; rw [add_comm]
  nsmul := nsmulRec

/-- • distributes over + -/
instance : DistribMulAction ℝ (Prob ℝ) where
  one_smul x := by simp only [smul_eq, one_mul, bind_pure]
  mul_smul a b x := by simp only [mul_eq, smul_eq, bind_pure, bind_assoc, pure_bind, mul_assoc]
  smul_zero x := by simp only [smul_eq, zero_eq, pure_bind, mul_zero]
  smul_add a x y := by simp only [smul_eq, add_eq, bind_assoc, pure_bind, mul_add]

/-- map.exp is exp of composition -/
lemma exp_map (f : α → β) (g : Prob α) (h : β → ℝ) : (f <$> g).exp h = g.exp (h ∘ f) := by
  simp only [map_eq, exp_bind, exp_pure]; rfl

-- Basics of mean
lemma mean_pure (x : ℝ) : (pure x : Prob ℝ).mean = x := by simp only [mean, exp_pure, id]
lemma mean_bind (f : Prob α) (g : α → Prob ℝ) : (f >>= g).mean = f.exp (λ x ↦ (g x).mean) := by
  simp only [mean, exp_bind]
lemma mean_map (f : α → ℝ) (g : Prob α) : (f <$> g).mean = g.exp f := by
  simp only [mean, exp_map, Function.comp, id]

-- Expectation is linear (weak version for independent events)
lemma exp_const_mul (s : ℝ) (f : Prob α) (g : α → ℝ) :
    f.exp (λ x ↦ s * g x) = s * f.exp (λ x ↦ g x) := by
  simp only [exp, ←mul_assoc _ s _, mul_comm _ s, mul_assoc s _ _, ←Finsupp.mul_sum]
lemma exp_mul_const (s : ℝ) (f : Prob α) (g : α → ℝ) :
    f.exp (λ x ↦ g x * s) = f.exp (λ x ↦ g x) * s := by
  simp only [mul_comm _ s, exp_const_mul]
lemma exp_div (s : ℝ) (f : Prob α) (g : α → ℝ) : f.exp (λ x ↦ g x / s) = f.exp (λ x ↦ g x) / s := by
  simp only [div_eq_inv_mul, exp_const_mul]
lemma exp_add (f : Prob α) (g h : α → ℝ) : f.exp (λ x ↦ g x + h x) = f.exp g + f.exp h := by
  simp only [exp, mul_add]; exact Finset.sum_add_distrib
lemma exp_const_add (f : Prob α) (g : ℝ) (h : α → ℝ) : f.exp (λ x ↦ g + h x) = g + f.exp h := by
  simp only [exp_add, exp_const]
lemma exp_add_const (f : Prob α) (g : α → ℝ) (h : ℝ) : f.exp (λ x ↦ g x + h) = f.exp g + h := by
  simp only [exp_add, exp_const]

-- Expectation is monotonic
lemma exp_mono {f : Prob α} {g h : α → ℝ} (gh : ∀ x, f.prob x ≠ 0 → g x ≤ h x) :
    f.exp g ≤ f.exp h := by
  simp only [exp]; apply Finset.sum_le_sum; intro x m
  exact mul_le_mul_of_nonneg_left (gh x (mem_iff.mp m)) (prob_nonneg _)
lemma exp_nonneg {f : Prob α} {g : α → ℝ} (g0 : ∀ x, f.prob x ≠ 0 → 0 ≤ g x) : 0 ≤ f.exp g := by
  have m := exp_mono g0; simp only [exp_const] at m; exact m

/-- Expectation is monotonic, general version for different distributions -/
lemma exp_mono' {f g : Prob α} (u v : α → ℝ) (h : ∀ x, f.prob x * u x ≤ g.prob x * v x) :
    f.exp u ≤ g.exp v := by
  simp only [exp, Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_union_left f.prob.support g.prob.support),
    Finset.sum_subset (Finset.subset_union_right f.prob.support g.prob.support)]
  · apply Finset.sum_le_sum; intro _ _; apply h
  · intro x _ m; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m; simp only [m, zero_mul]
  · intro x _ m; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m; simp only [m, zero_mul]

/-- Upper bounding an expectation by bounding each element -/
lemma exp_le_of_forall_le {f : Prob α} {u : α → ℝ} {b : ℝ} (h : ∀ x, f.prob x ≠ 0 → u x ≤ b) :
    f.exp u ≤ b := by
  rw [←exp_const f b]; exact exp_mono h

/-- Lower bounding an expectation by bounding each element -/
lemma le_exp_of_forall_le {f : Prob α} {u : α → ℝ} {b : ℝ} (h : ∀ x, f.prob x ≠ 0 → b ≤ u x) :
    b ≤ f.exp u := by
  rw [←exp_const f b]; exact exp_mono h

-- Mean is linear
lemma mean_smul (s : ℝ) (f : Prob ℝ) : (s • f).mean = s * f.mean := by
  simp only [mean, smul_eq, exp_bind, exp_pure, id, exp_const_mul s f (λ x ↦ x)]
  rfl
lemma mean_add (f g : Prob ℝ) : (f + g).mean = f.mean + g.mean := by
  simp only [mean, add_eq, exp_bind, exp_pure, id, λ x ↦ exp_add g (λ _ ↦ x) (λ y ↦ y), exp_const,
    exp_add]
  rfl

/-- Mean is multiplicative -/
lemma mean_mul (f g : Prob ℝ) : (f * g).mean = f.mean * g.mean := by
  simp only [mean, mul_eq, exp_bind, exp_pure, id, ←exp_mul_const]; simp only [←exp_const_mul]
  rfl

-- f.pr is between 0 and 1
lemma pr_nonneg {f : Prob α} {p : α → Prop} : 0 ≤ f.pr p := by
  simp only [pr]; apply exp_nonneg; intro x _; split; norm_num; rfl
lemma pr_le_one {f : Prob α} {p : α → Prop} : f.pr p ≤ 1 := by
  simp only [pr]; apply le_trans (@exp_mono _ f _ (λ _ ↦ 1) _)
  · simp only [exp_const]; rfl
  · intro x _; split; rfl; norm_num
lemma pr_mem_Icc {f : Prob α} {p : α → Prop} : f.pr p ∈ Icc 0 1 :=
  ⟨pr_nonneg, pr_le_one⟩

/-- pr of a constant prop is either 1 or 0 -/
lemma pr_const (f : Prob α) (p : Prop) : f.pr (λ _ ↦ p) = if p then (1:ℝ) else 0 := by
  simp only [pr, exp_const]

/-- pr is monotonic -/
lemma pr_mono {f : Prob α} {p q : α → Prop} (pq : ∀ x, f.prob x ≠ 0 → p x → q x) :
    f.pr p ≤ f.pr q := by
  apply exp_mono; intro x m; rw [ite_le_ite_iff]; exact pq x m

/-- (pure x).pr p = if p x else 1 else 0 -/
lemma pr_pure {x : α} (p : α → Prop) : (pure x : Prob α).pr p = if p x then 1 else 0 := by
  simp only [pr, exp_pure]

/-- (f >>= g).pr works as expected -/
lemma pr_bind {f : Prob α} {g : α → Prob β} (p : β → Prop) :
    (f >>= g).pr p = f.exp (λ x ↦ (g x).pr p) := by
  simp only [pr, exp_bind]

/-- (f <$> g).pr works as expected -/
lemma pr_map {f : α → β} {g : Prob α} (p : β → Prop) : (f <$> g).pr p = g.pr (λ x ↦ p (f x)) := by
  simp only [pr, exp_map, Function.comp]

/-- f.exp g < f.exp h if g ≤ h and g x < h x on at least one nonzero probability x -/
lemma exp_lt_exp {f : Prob α} {g h : α → ℝ} (le : ∀ x, f.prob x ≠ 0 → g x ≤ h x)
    (lt : ∃ x, f.prob x ≠ 0 ∧ g x < h x) : f.exp g < f.exp h := by
  apply Finset.sum_lt_sum
  · intro x m; exact mul_le_mul_of_nonneg_left (le x (mem_iff.mp m)) (prob_nonneg _)
  · rcases lt with ⟨x,px,lt⟩; use x, mem_iff.mpr px
    exact mul_lt_mul_of_pos_left lt (px.symm.lt_of_le (prob_nonneg _))

-- f.pr True = 1, resp False
lemma pr_false {f : Prob α} : f.pr (λ _ ↦ False) = 0 := by simp only [pr, exp_const, if_false]
lemma pr_true {f : Prob α} : f.pr (λ _ ↦ True) = 1 := by simp only [pr, exp_const, if_true]

/-- f.pr p < f.pr q if p ≤ q and p x < q x on at least one nonzero probability x -/
lemma pr_lt_pr {f : Prob α} {p q : α → Prop} (le : ∀ x, f.prob x ≠ 0 → p x → q x)
    (lt : ∃ x, f.prob x ≠ 0 ∧ ¬p x ∧ q x) : f.pr p < f.pr q := by
  apply exp_lt_exp
  · intro x m; rw [ite_le_ite_iff]; exact le x m
  · rcases lt with ⟨x,m,px,qx⟩; use x,m; simp only [px, qx, if_true, if_false, zero_lt_one]

/-- Pull ∧ const out of a pr -/
lemma pr_and_const {f : Prob α} {p : α → Prop} {q : Prop} :
    f.pr (λ x ↦ p x ∧ q) = f.pr p * (if q then 1 else 0) := by
  by_cases h : q
  repeat simp only [h, and_true, if_true, mul_one, and_false, pr_false, if_false, mul_zero]

/-- f.exp u = 0 in terms of forall -/
lemma exp_eq_zero {f : Prob α} {u : α → ℝ} (u0 : ∀ x, f.prob x ≠ 0 → u x = 0) : f.exp u = 0 := by
  rw [←exp_const f 0]; exact exp_congr u0

/-- f.pr p = 0 in terms of forall -/
lemma pr_eq_zero {f : Prob α} {p : α → Prop} : f.pr p = 0 ↔ ∀ x, f.prob x ≠ 0 → ¬p x := by
  constructor
  · intro h; contrapose h; simp only [not_forall] at h ⊢; apply ne_of_gt
    rcases h with ⟨x,px,h⟩; rw [not_not] at h; rw [←pr_false]; apply pr_lt_pr
    · simp only [ne_eq, IsEmpty.forall_iff, implies_true]
    · simp only [ne_eq, not_false_eq_true, true_and]; use x, px, h
  · intro h; rw [←pr_false]; apply pr_congr; simp only [iff_false]; exact h

/-- `pr ≠ 0` if there is some nonzero prob -/
lemma pr_ne_zero (f : Prob α) (p : α → Prop) : f.pr p ≠ 0 ↔ ∃ x, f.prob x ≠ 0 ∧ p x := by
  simp only [ne_eq, pr_eq_zero, not_forall, not_not, exists_prop]

/-- f.pr p = 1 in terms of forall -/
lemma pr_eq_one {f : Prob α} {p : α → Prop} : f.pr p = 1 ↔ ∀ x, f.prob x ≠ 0 → p x := by
  constructor
  · intro h; contrapose h; simp only [not_forall] at h ⊢; apply ne_of_lt
    rcases h with ⟨x,px,h⟩; rw [←pr_true]; apply pr_lt_pr
    · simp only [implies_true]
    · use x, px
  · intro h; rw [←pr_true]; apply pr_congr; simp only [iff_true]; exact h

/-- f.pr ¬p = 1 - f.pr p -/
lemma pr_neg {f : Prob α} {p : α → Prop} : f.pr (λ x ↦ ¬p x) = 1 - f.pr p := by
  rw [eq_sub_iff_add_eq, ←pr_true]; simp only [pr, ←exp_add]; apply exp_congr;
  intro x _; simp only [if_true]; by_cases h : p x
  repeat simp [h]
lemma pr_neg' {f : Prob α} {p : α → Prop} : f.pr p = 1 - f.pr (λ x ↦ ¬p x) := by
  simp only [pr_neg, sub_sub_cancel]

/-- pr (p ∨ q) ≤ pr p + pr q -/
lemma pr_or_le {f : Prob α} (p q : α → Prop) : f.pr (λ x ↦ p x ∨ q x) ≤ f.pr p + f.pr q := by
  simp only [pr, ←exp_add]; apply exp_mono; intro x _
  by_cases px : p x
  · by_cases qx : q x
    · simp only [px, qx, or_self, ite_true, le_add_iff_nonneg_right, zero_le_one]
    · simp only [px, qx, or_false, ite_true, ite_false, add_zero, le_refl]
  · by_cases qx : q x
    . simp only [px, qx, or_true, ite_true, ite_false, zero_add, le_refl]
    · simp only [px, qx, or_self, ite_false, add_zero, le_refl]

/-- Split a pr into two using another event -/
lemma pr_eq_add_of_cut {f : Prob α} {p : α → Prop} (q : α → Prop) :
    f.pr p = f.pr (fun x ↦ p x ∧ q x) + f.pr (fun x ↦ p x ∧ ¬q x) := by
  simp only [pr, ←exp_add]; apply exp_congr; intro x _; by_cases px : p x;
  repeat { by_cases qx : q x; repeat simp [px, qx] }

/-- Markov's inequality -/
lemma markov' (f : Prob α) (g : α → ℝ) (f0 : ∀ x, f.prob x ≠ 0 → 0 ≤ g x) {a : ℝ} (a0 : 0 < a) :
    f.pr (λ x ↦ a ≤ g x) ≤ f.exp g / a := by
  simp only [le_div_iff a0, pr, mean, ←exp_mul_const, ite_mul, one_mul, zero_mul, id];
  apply exp_mono; intro x m; split; assumption; exact f0 _ m
lemma markov (f : Prob ℝ) (f0 : ∀ x, f.prob x ≠ 0 → 0 ≤ x) {a : ℝ} (a0 : 0 < a) :
    f.pr (λ x ↦ a ≤ x) ≤ f.mean / a :=
  f.markov' _ f0 a0

/-- Lower bounding an exp in terms of an event -/
lemma le_exp_of_cut {f : Prob α} {u : α → ℝ} (i : α → Prop) (a b : ℝ) (fi : a ≤ f.pr i)
    (iu : ∀ x, f.prob x ≠ 0 → i x → b ≤ u x) (u0 : ∀ x, f.prob x ≠ 0 → ¬i x → 0 ≤ u x)
    (b0 : 0 ≤ b) : a * b ≤ f.exp u := by
  have h : ∀ x, f.prob x ≠ 0 → b * (if i x then 1 else 0) ≤ u x := by
    intro x fx; by_cases ix : i x
    · simp only [ix, if_true, mul_one]; exact iu x fx ix
    · simp only [ix, if_false, pr_nonneg, mul_zero]; exact u0 x fx ix
  refine le_trans ?_ (exp_mono h)
  rw [exp_const_mul, ←pr, mul_comm]
  exact mul_le_mul_of_nonneg_left fi b0

/-- Lower bounding a pr bind in terms of a middle event -/
lemma le_pr_bind_of_cut {f : Prob α} {g : α → Prob β} {p : β → Prop} {i : α → Prop} (a b : ℝ)
    (fi : a ≤ f.pr i) (gp : ∀ x, f.prob x ≠ 0 → i x → b ≤ (g x).pr p) (b0 : 0 ≤ b) :
    a * b ≤ (f >>= g).pr p := by
  simp only [pr_bind]; exact le_exp_of_cut i a b fi gp (λ _ _ _ ↦ pr_nonneg) b0

/-- pr/exp of an indicator is just prob -/
lemma pr_eq_prob (f : Prob α) (y : α) : f.pr (λ x ↦ x = y) = f.prob y := by
  simp only [pr, exp]; by_cases m : y ∈ f.supp
  · rw [Finsupp.sum, Finset.sum_eq_single y]; simp only [ite_true, mul_one, prob]
    · intro z _ zy; simp only [zy, if_false, mul_zero]
    · intro n; simp only [m] at n
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at n; simp only [n, ite_true, mul_one]
  · rw [Finsupp.sum, Finset.sum_eq_zero]; rw [mem_iff, not_not] at m; exact m.symm
    intro z n; by_cases zy : z = y
    · simp only [supp, Finsupp.mem_support_iff, not_not, zy] at m n; simp only [n] at m
    · simp only [zy, if_false, mul_zero]
lemma exp_eq_prob (f : Prob α) (y : α) {d : ∀ x, Decidable (x = y)} :
    f.exp (λ x ↦ @ite _ (x = y) (d _) (1:ℝ) 0) = f.prob y := by
  rw [←pr_eq_prob f y]; apply exp_congr; intro x _; rw [ite_one_zero_congr]

/-- `f.exp u = 0` in terms of forall, for nonnegative `u` -/
lemma exp_eq_zero_iff {f : Prob α} {u : α → ℝ} (h : ∀ x, f.prob x ≠ 0 → 0 ≤ u x) :
    f.exp u = 0 ↔ ∀ x, f.prob x ≠ 0 → u x = 0 := by
  constructor
  · intro h; contrapose h; simp only [not_forall] at h; apply ne_of_gt
    rcases h with ⟨x,px,ux⟩
    refine lt_of_lt_of_le ?_ (le_exp_of_cut (fun y ↦ y = x) (f.prob x) (u x) ?_ ?_ ?_ ?_)
    · apply mul_pos; exact px.symm.lt_of_le (prob_nonneg _); exact (Ne.symm ux).lt_of_le (h _ px)
    · simp only [pr_eq_prob, le_refl]
    · intro y _ e; rw [e]
    · intro y py _; exact h _ py
    · exact h _ px
  · exact exp_eq_zero

/-- Fintype expectations -/
lemma exp_fintype (f : Prob α) [Fintype α] (g : α → ℝ) :
    f.exp g = Finset.univ.sum (fun x ↦ f.prob x * g x) := by
  simp only [exp, Finsupp.sum]; rw [Finset.sum_subset (Finset.subset_univ _)]
  · intro _ _ m; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m; simp only [m, zero_mul]

/-- Boolean expectations -/
lemma exp_bool (f : Prob Bool) (g : Bool → ℝ) :
    f.exp g = f.prob false * g false + f.prob true * g true := by
  simp only [exp_fintype, Fintype.sum_bool, add_comm]

-- Given a bind, enrich the output type to include the intermediate type.  This lets us do
-- probability calculations in a measure space that "includes the trace".
lemma exp_enrich {f : Prob α} {g : α → Prob β} {u : β → ℝ} :
    (f >>= g).exp u = (f >>= (λ x ↦ Prod.mk x <$> g x)).exp (λ y ↦ u y.2) := by
  simp only [exp_bind, exp_map]; apply exp_congr; intro x _; apply exp_congr; intro y _; rfl
lemma pr_enrich {f : Prob α} {g : α → Prob β} {p : β → Prop} :
    (f >>= g).pr p = (f >>= (λ x ↦ Prod.mk x <$> g x)).pr (λ y ↦ p y.2) := by
  simp only [pr_bind, pr_map]
lemma cexp_enrich {f : Prob α} {g : α → Prob β} {u : β → ℝ} {q : β → Prop} :
    (f >>= g).cexp u q = (f >>= (λ x ↦ Prod.mk x <$> g x)).cexp (λ y ↦ u y.2) (λ y ↦ q y.2) := by
  rw [cexp, cexp, exp_enrich, pr_enrich]

/-- Bound one exp in terms of another on a different space by injecting between the spaces -/
lemma exp_le_exp_of_map {f : Prob α} {g : Prob β} {u : α → ℝ} {v : β → ℝ} (i : α → β)
    (inj : ∀ x0 x1, f.prob x0 * u x0 ≠ 0 → f.prob x1 * u x1 ≠ 0 → i x0 = i x1 → x0 = x1)
    (uv : ∀ x, f.prob x * u x ≠ 0 → f.prob x * u x ≤ g.prob (i x) * v (i x))
    (v0 : ∀ y, g.prob y ≠ 0 → 0 ≤ v y) : f.exp u ≤ g.exp v := by
  simp only [exp, Finsupp.sum]
  apply Finset.sum_le_sum_of_map i inj uv
  · intro y m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_mul]
  · intro y m; simp only [Finsupp.mem_support_iff] at m; apply mul_nonneg (prob_nonneg _) (v0 _ m)

/-- `(f >>= g).prob y ≠ 0` iff there is nonzero prob intermediate `x` -/
lemma prob_bind_ne_zero (f : Prob α) (g : α → Prob β) (y : β) :
    (f >>= g).prob y ≠ 0 ↔ ∃ x, f.prob x ≠ 0 ∧ (g x).prob y ≠ 0 := by
  constructor
  · intro h; contrapose h
    simp only [ne_eq, not_exists, not_and, not_not, prob_bind] at h ⊢
    exact exp_eq_zero h
  · intro ⟨x,f0,g0⟩
    refine (lt_of_lt_of_le (mul_pos ?_ ?_) (le_prob_bind_of_cut x)).ne'
    · exact f0.symm.lt_of_le (prob_nonneg _)
    · exact g0.symm.lt_of_le (prob_nonneg _)

end Prob
