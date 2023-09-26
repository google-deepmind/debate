import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Misc.Finset
import Prob.Basics

/-!
`Prob` injects into `Pmf`
-/

open Classical
open Set
open scoped Real Topology
noncomputable section

variable {α β γ : Type}

/-- Turn a `Prob` into a `Pmf` -/
def Prob.toPmf (f : Prob α) : Pmf α where
  val x := .ofReal (f.prob x)
  property := by
    have e : f.supp.sum (fun x => ENNReal.ofReal (f.prob x)) = 1 := by
      have t := f.total; simp only [Finsupp.sum] at t
      simp only [Finset.sum_ofReal (fun _ ↦ prob_nonneg _), supp, t, ENNReal.ofReal_one]
    rw [←e]; apply Finset.hasSum_sum;
    intro x m; simp only [mem_iff, not_not] at m; simp only [m, ENNReal.ofReal_zero]

/-- Turn a finitely supported `Pmf` into a `Prob` -/
def Pmf.toProb (f : Pmf α) (finite : f.support.Finite) : Prob α where
  prob := by
    apply Finsupp.ofSupportFinite (fun x ↦ ENNReal.toReal (f x))
    rcases finite.exists_finset with ⟨s,h⟩
    apply Set.Finite.ofFinset s
    intro x; simp only [h, Pmf.mem_support_iff, ne_eq, Function.mem_support, ENNReal.toReal_eq_zero_iff,
      Pmf.apply_ne_top, or_false]
  prob_nonneg := by intro x; simp only [Finsupp.ofSupportFinite_coe]; apply ENNReal.toReal_nonneg
  total := by
    rcases finite.exists_finset with ⟨s,h⟩
    apply eq_of_forall_dist_le; intro e ep
    set e' : ENNReal := .ofReal e
    have e0' : e' ≠ 0 := (ENNReal.ofReal_pos.mpr ep).ne'
    have m : 1 ∈ Ioo (1-e' : ENNReal) (1+e') := by
      simp only [ge_iff_le, gt_iff_lt, not_lt, mem_Ioo]; constructor
      · apply ENNReal.sub_lt_self; norm_num; norm_num; exact e0'
      · apply ENNReal.lt_add_right; norm_num; exact e0'
    rcases tendsto_atTop_nhds.mp f.property (Ioo (1-e') (1+e')) m isOpen_Ioo with ⟨t,total⟩
    · specialize total (s ∪ t) (Finset.subset_union_right _ _)
      rw [←Finset.sum_subset (Finset.subset_union_left _ _)] at total
      · simp only [Finsupp.sum, Finsupp.ofSupportFinite_coe]
        rw [@Finset.sum_subset _ _ _ s]
        · simp only [ge_iff_le, gt_iff_lt, not_lt, mem_Ioo] at total
          simp only [Finset.sum_toReal (λ _ ↦ Pmf.apply_ne_top _ _), Real.dist_eq, abs_le, le_sub_iff_add_le,
            sub_le_iff_le_add, add_comm _ (1:ℝ)]
          constructor
          · rw [←ENNReal.ofReal_le_iff_le_toReal]
            · rw [←sub_eq_add_neg, ENNReal.ofReal_sub, ENNReal.ofReal_one]; exact le_of_lt total.1
              exact le_of_lt ep
            · apply Finset.sum_ne_top; intro x; apply Pmf.apply_ne_top
          · apply ENNReal.toReal_le_of_le_ofReal
            · exact add_nonneg (by norm_num) (le_of_lt ep)
            · rw [ENNReal.ofReal_add, ENNReal.ofReal_one]; exact le_of_lt total.2
              · norm_num
              · exact le_of_lt ep
        · intro x
          simp only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, h, ENNReal.toReal_ne_zero,
            Pmf.mem_support_iff]
          apply And.left
        · intro x _ m; simpa only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq, not_not] using m
      · intro x _ m; simpa only [h x, Pmf.mem_support_iff, not_not] using m

/-- `Prob.toPmf` has the expected coe -/
@[simp] lemma Prob.toPmf_coe (f : Prob α) (x : α) : f.toPmf x = ENNReal.ofReal (f.prob x) := rfl

/-- `Pmf.toProb` has the expected prob -/
@[simp] lemma Pmf.prob_toProb (f : Pmf α) (h : f.support.Finite) (x : α) :
    (f.toProb h).prob x = ENNReal.toReal (f x) := rfl

/-- `Prob.toPmf` has finite support -/
lemma Prob.toPmf_support_finite (f : Prob α) : f.toPmf.support.Finite := by
  apply Set.Finite.ofFinset f.supp; intro x
  simp only [mem_iff, ne_eq, Pmf.mem_support_iff, toPmf_coe, ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro h; exact Ne.lt_of_le (Ne.symm h) (prob_nonneg _)
  · intro h; exact h.ne'

/-- `Prob → Pmf → Prob` is the identity -/
theorem Prob.toProb_toPmf (f : Prob α) : f.toPmf.toProb f.toPmf_support_finite = f := by
  ext; simp only [Pmf.prob_toProb, toPmf_coe, ENNReal.toReal_ofReal_eq_iff]; apply prob_nonneg

/-- `Prob.toPmf` commutes with pure -/
lemma Prob.pure_toPmf (x : α) : (pure x : Prob α).toPmf = pure x := by
  ext y; simp only [toPmf_coe, prob_pure, Pmf.instMonadPmf, Pmf.pure_apply]
  split_ifs; simp only [ENNReal.ofReal_one]; simp only [ENNReal.ofReal_zero]

/-- `Prob.toPmf` commutes with bind -/
lemma Prob.bind_toPmf (f : Prob α) (g : α → Prob β) : (f >>= g).toPmf = f.toPmf >>= (fun x ↦ (g x).toPmf) := by
  ext y
  simp only [Prob.toPmf_coe, Pmf.instMonadPmf, Pmf.bind_apply, Prob.prob_bind, Prob.exp, Finsupp.sum,
    ←Finset.sum_ofReal fun _ ↦ mul_nonneg (prob_nonneg _) (prob_nonneg _), ←ENNReal.ofReal_mul (prob_nonneg _)]
  refine (HasSum.tsum_eq ?_).symm; apply Finset.hasSum_sum
  intro _ m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_mul, ENNReal.ofReal_zero]
