import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

/-!
Finset facts
-/

open Classical
open Option (some none)
open scoped Real
noncomputable section

variable {α β : Type}

/-- We can swap one set for another in Finset.sum if the function is zero away from their intersection -/
lemma Finset.sum_eq_sum_zero_off_inter {s0 s1 : Finset α} {g : α → ℝ} (h : ∀ x, x ∉ s0 ∨ x ∉ s1 → g x = 0) :
    s0.sum g = s1.sum g := by
  have e0 : s0.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_union_left _ _)
    · intro x m; apply h; left; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  have e1 : s1.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_union_right _ _)
    · intro x m; apply h; right; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  rw [e0, e1]

/-- Bound one Finset.sum in terms of another on a different space, but injecting between the spaces -/
lemma Finset.sum_le_sum_of_map {s : Finset α} {t : Finset β} {u : α → ℝ} {v : β → ℝ} (i : α → β)
    (inj : ∀ x0 x1, u x0 ≠ 0 → u x1 ≠ 0 → i x0 = i x1 → x0 = x1)
    (le : ∀ x, u x ≠ 0 → u x ≤ v (i x))
    (tv : ∀ y, y ∉ t → v y = 0)
    (v0 : ∀ y, y ∈ t → 0 ≤ v y) :
    s.sum u ≤ t.sum v := by
  rw [←Finset.sum_filter_ne_zero]
  set s' := s.filter (λ x ↦ u x ≠ 0)
  have e : t.sum v = (s'.image i).sum v + (t \ s'.image i).sum v := by
    rw [←Finset.sum_union disjoint_sdiff]; apply Finset.sum_subset_zero_on_sdiff
    · simp only [union_sdiff_self_eq_union, Finset.subset_union_right]
    · intro y m; simp only [union_sdiff_self_eq_union, mem_sdiff, mem_union] at m
      exact tv _ m.2
    · intro _ _; rfl
  rw [e]; clear e
  refine' le_trans _ (le_add_of_nonneg_right _)
  · rw [Finset.sum_image]
    · apply Finset.sum_le_sum; intro x m; simp only [mem_filter] at m; exact le _ m.2
    · intro x m y n; simp only [mem_filter] at m n; apply inj _ _ m.2 n.2
  · apply Finset.sum_nonneg; intro y m; simp only [mem_sdiff, not_exists, not_and] at m; exact v0 _ m.1
