import Debate.Protocol
import Prob.Arith
import Prob.Chernoff
import Prob.Cond
import Misc.Finset
import Misc.If

/-!
Correctness of the stochastic oracle doubly-efficient debate algorithm (details)
See Correct.lean for the summary
-/

-- Work around https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- See issue lean4#2220

open Classical
open Prob
open Option (some none)
open Real (log)
open Set
open scoped Real
noncomputable section

variable {n t : ℕ}

-- We first show that Honest Alice, Bob, and Vera do their jobs correctly to
-- within the necessary failure probabilities.

/-- samples' is samples without the Nat.ceil -/
def samples' (d : ℕ) (e : ℝ) : ℝ := (-2:ℝ) * (d:ℝ)^2 * Real.log (e/2)
lemma le_samples (d : ℕ) (e : ℝ) : samples' d e ≤ samples d e := Nat.le_ceil _

/-- round x = y if |x - y| < 1/2 -/
lemma round_eq_of_abs_lt (x : ℝ) (y : ℤ) (h : |x-y| < 1/2) : round x = y := by
  simp only [round_eq, Int.floor_eq_iff, abs_lt] at h ⊢; constructor
  repeat { linarith }

/-- Honest Alice usually gives the correct p -/
lemma alice_prob' (o : Oracle) (d : ℕ) [od : Discrete o d] {e : ℝ} (e0 : 0 < e) (y : Vector Bool n) :
    (alice' o d e _ y).pr (λ p ↦ p ≠ (o y.toList).prob true) ≤ e := by
  rcases od.disc y.toList true with ⟨k,hk⟩
  simp only [alice', pr_bind, pr_pure]
  have t0 : 0 ≤ (1:ℝ) / (2*d) := div_nonneg (by norm_num) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  refine' le_trans _ (le_trans (chernoff_estimate_abs_le (o y.toList) (samples d e) t0) _)
  · simp only [Prob.pr]; apply exp_mono; intro x _; rw [ite_le_ite_iff]; intro h
    contrapose h; simp only [not_not, not_le, hk] at h ⊢
    suffices r : round (x * d) = k; simp only [r, Int.cast_ofNat]
    apply round_eq_of_abs_lt
    rw [←mul_div_cancel x (ne_of_gt od.d0), ←sub_div, abs_div, abs_of_pos od.d0, div_mul_eq_div_div,
      div_lt_div_right od.d0] at h
    exact h
  · have le : (-2:ℝ) * ↑(samples d e) * (1 / (2*(d:ℝ)))^2 ≤ (-2:ℝ) * samples' d e * (1 / (2*(d:ℝ)))^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left (le_samples _ _) (by norm_num)) (sq_nonneg _)
    refine' le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr le) (by norm_num)) _
    simp only [samples', div_pow, mul_pow, one_pow, mul_div, mul_one, pow_two (2:ℝ), ←mul_assoc]; norm_num
    rw [mul_comm _ (log _), mul_div_assoc, Real.exp_mul, Real.exp_log (half_pos e0), div_self, Real.rpow_one]
    · ring_nf; rfl
    · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt od.d0))

lemma alice_e0 (t : ℕ) : 0 < 1 / (10*(t+1:ℝ)) := one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_add_one_pos _))

lemma alice_prob (o : Oracle) (d : ℕ) [Discrete o d] (t : ℕ) (y : Vector Bool n) :
    (alice o d t _ y).pr (λ p ↦ p ≠ (o y.toList).prob true) ≤ 1 / (10*(t+1:ℝ)) := alice_prob' _ _ (alice_e0 _) _

/-- Honest Bob is usually correct about whether p is correct -/
lemma bob_prob' (o : Oracle) (d : ℕ) [Discrete o d] {e : ℝ} (e0 : 0 < e) (y : Vector Bool n) (p : ℝ) :
    (bob' o d e _ y p).pr (λ x ↦ x ≠ (p = (o y.toList).prob true)) ≤ e := by
  simp only [bob', pr_bind]
  refine' le_trans _ (alice_prob' o d e0 y)
  apply exp_mono; intro q _;
  simp only [pr_pure, Ne.def, decide_eq_decide, ite_le_ite_iff]
  by_cases e : q = (o y.toList).prob true
  repeat { simp only [e, implies_true] }

lemma bob_prob (o : Oracle) (d : ℕ) [Discrete o d] (t : ℕ) (y : Vector Bool n) (p : ℝ) :
    (bob o d t _ y p).pr (λ x ↦ x ≠ (p = (o y.toList).prob true)) ≤ 1 / (10*(t+1:ℝ)) := bob_prob' _ _ (alice_e0 _) _ _

/-- Vera is usually correct, as they're just a weak Bob -/
lemma vera_prob (o : Oracle) (d : ℕ) [Discrete o d] (y : Vector Bool n) (p : ℝ) :
    (vera o d y p).pr (λ x ↦ x ≠ (p = (o y.toList).prob true)) ≤ 1/9 := bob_prob' _ _ (by norm_num) _ _

-- As written above the debate protocol is awkward to analyze, since Alice's and Bob's moves are
-- interleaved and intermediate states are discarded.  Therefore, we rewrite it into a form where
-- Alice moves first, then Bob moves.

/-- All of Alice's moves, and the resulting trace -/
def alices (alice : Alice) : (n : ℕ) → Prob (Vector ℝ n × Vector Bool n)
| 0 => pure (Vector.nil, Vector.nil)
| n+1 => do
  let (p,y) ← alices alice n
  let q ← alice _ y
  let x ← bernoulli q
  return (q ::ᵥ p, x ::ᵥ y)

/-- All of Bob's moves, after Alice's -/
def bobs (o : Oracle) (d : ℕ) (bob : Bob) {n : ℕ} (p : Vector ℝ n) (y : Vector Bool n) : Prob (Option Bool) :=
  match n with
  | 0 => pure none
  | _+1 => do match ←bobs o d bob p.tail y.tail with
    | some r => return r
    | none => do
      let b ← bob _ y.tail p.head
      return if b then none else some (←vera o d y.tail p.head)

/-- All of Alice's moves prior to Bob's, producing the full trace -/
def trace (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) (t : ℕ) :
    Prob ((Vector ℝ (t+1) × Vector Bool (t+1)) × Option Bool) := do
  let a ← alices alice (t+1)
  Prod.mk a <$> bobs o d bob a.1 a.2

/-- Extract the final result -/
def extract (x : (Vector ℝ (t+1) × Vector Bool (t+1)) × Option Bool) : Bool := match x.2 with
  | none => x.1.2.head
  | some r => r

/-- debate, with all of Alice's moves prior to Bob's, and producing the full trace -/
def transposed (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) (t : ℕ) : Prob Bool :=
  extract <$> trace o d alice bob t

/-- Shim to turn alices >>= bobs into steps -/
def shim {n : ℕ} (y : Vector Bool n) : Option Bool → State n
| some r => Except.error r
| none => Except.ok y

/-- The transposed formulation of debate is the same -/
lemma debate_eq_transposed (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) (t : ℕ) :
    debate o d alice bob t = transposed o d alice bob t := by
  have h : ∀ n, steps o d alice bob n = alices alice n >>= λ (p,y) ↦ shim y <$> bobs o d bob p y := by
    intro n; induction' n with n h
    · simp only [steps, alices, pure_bind, bobs, shim, map_eq]
    · simp only [steps, h, alices, bobs, bind_assoc]; apply congr_arg₂ _ rfl; funext ⟨p,y⟩
      simp only [pure_bind, map_eq, bind_assoc, Vector.tail_cons, Vector.head_cons, bind_comm _ (bobs _ _ _ _ _)]
      apply congr_arg₂ _ rfl; funext r; match r with
      | some r => simp only [shim, pure_bind, bind_pure, bind_const]
      | none =>
        simp only [shim, step]; apply congr_arg₂ _ rfl; funext q
        simp only [bind_assoc, bind_comm _ (bob _ _ _)]; apply congr_arg₂ _ rfl; funext s
        match s with
        | true => simp only [if_true]; apply congr_arg₂ _ rfl; funext x; simp only [bind_const, pure_bind]
        | false => simp only [if_false, bind_const, pure_bind]
  simp only [debate, transposed, trace, extract, h, bind_assoc, map_eq]
  apply congr_arg₂ _ rfl; funext ⟨p,y⟩; apply congr_arg₂ _ rfl; funext r; match r with
  | some true => simp only [shim, pure_bind, Option.getD]
  | some false => simp only [shim, pure_bind, Option.getD]
  | none => simp only [shim, pure_bind, Option.getD]

-- Completeness.  We assume that
-- 1. Pr(final ≥ 2/3)
-- 2. Alice is honest.
-- 3. Bob is secretly Eve, and might be evil
-- Then we have
-- 1. Alice gives the right probabilities at all steps w.p. ≥ 9/10
-- 2. W.p. 2/3 of traces give true, so w.p. 3/5 Alice is correct and produces true
-- 3. If Alice is correct and produces true, Bob has to reject, but Vera yells w.p. ≥ 8/9

/-- The correct probabilities given a trace -/
def Oracle.probs (o : Oracle) {n : ℕ} (y : Vector Bool n) : Vector ℝ n := match n with
| 0 => Vector.nil
| _+1 => (o y.tail.toList).prob true ::ᵥ o.probs y.tail
lemma Oracle.probs_succ (o : Oracle) {n : ℕ} {y : Vector Bool (n+1)} :
    o.probs y = (o y.tail.toList).prob true ::ᵥ o.probs y.tail := rfl

/-- Lemmas about 1/10/(t+1) -/
lemma alice_div_lt_one {t : ℕ} : (1:ℝ)/10/(↑t+1) < 1 := by
  rw [div_lt_one (Nat.cast_add_one_pos _)]
  refine' lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg _))
lemma alice_div_pos {t : ℕ} : 0 < (1:ℝ)/10/(↑t+1) := div_pos (by norm_num) (Nat.cast_add_one_pos _)
lemma alice_sub_div_pos {t : ℕ} : 0 < 1 - (1:ℝ)/10/(↑t+1) := sub_pos.mpr alice_div_lt_one
lemma alice_sub_div_lt_one {t : ℕ} : 1 - (1:ℝ)/10/(↑t+1) < 1 := sub_lt_self _ alice_div_pos
lemma le_alice_pow {t : ℕ} : 9/10 ≤ (1 - 1/10/(↑t+1) : ℝ) ^ (t+1) := by
  refine' le_trans _ (one_add_mul_le_pow _ (t+1))
  · simp only [Nat.cast_add_one, mul_neg]; rw [mul_div_cancel' _ (Nat.cast_add_one_ne_zero _)]; norm_num
  · simp only [neg_le_neg_iff]; exact le_trans (le_of_lt alice_div_lt_one) (by norm_num)

/-- ∀ y, Alice produces (p,y) with p correct with probability ≥ 9/10 * o.prob y -/
lemma alices_correct (o : Oracle) (d t : ℕ) [Discrete o d] (y : Vector Bool (t+1)):
    9/10 * (o.fold (t+1)).prob y ≤ (alices (alice o d t) (t+1)).prob (o.probs y, y) := by
  suffices h : ∀ n z,
      (1 - 1/10/(t+1) : ℝ) ^ n * (o.fold n).prob z ≤ (alices (alice o d t) n).prob (o.probs z, z) by
    exact le_trans (mul_le_mul_of_nonneg_right le_alice_pow (prob_nonneg _)) (h (t+1) y)
  intro n; induction' n with n h
  · simp only [Nat.zero_eq, alices, prob_pure, Oracle.probs, Prod.ext_iff, true_and, Vector.eq_nil, if_true,
      pow_zero, one_mul]
    norm_num; apply prob_le_one
  · intro y; simp only [alices, Oracle.fold, prob_bind, ←exp_const_mul]
    apply exp_le_exp_of_map (λ z ↦ (o.probs z, z))
    · intro a b; simp only [Prod.mk.injEq, and_imp, imp_self, implies_true]
    · intro x _
      simp only [exp_const_mul, ←mul_assoc, prob_pure, Vector.eq_cons_iff, ite_and_one_zero, exp_mul_const,
        Prod.ext_iff]
      by_cases yx : y.tail = x
      · simp only [yx, if_true, mul_one, @eq_comm _ y.head, exp_eq_prob, Oracle.probs, Vector.head_cons,
          Vector.tail_cons]
        have e : ∀ z, (if (o x.toList).prob true = z then 1 else 0) * (bernoulli z).prob y.head =
            (if z = (o x.toList).prob true then 1 else 0) * (bernoulli ((o x.toList).prob true)).prob y.head := by
          intro z; by_cases h : z = (o x.toList).prob true
          · simp only [h, if_false, zero_mul]
          · simp only [h, Ne.symm h, if_false, zero_mul]
        simp only [e, exp_mul_const, exp_eq_prob, ←eq_bernoulli]; clear e yx
        simp only [pow_succ']; rw [←mul_assoc, mul_comm _ (_ ^ _), mul_assoc _ _ (prob _ y.head)]
        refine' mul_le_mul (h x) _ _ (prob_nonneg _)
        · refine' mul_le_mul_of_nonneg_right _ (prob_nonneg _)
          have a := alice_prob o d t x
          simp only [pr_neg, pr_eq_prob, ←div_div] at a
          linarith
        · exact mul_nonneg (le_of_lt alice_sub_div_pos) (prob_nonneg _)
      · simp only [yx, if_false, mul_zero, le_refl]
    · intro _ _; apply exp_nonneg; intro _ _; apply exp_nonneg; intro _ _; exact prob_nonneg _

/-- Alice is good (produces a winning trace with correct probs) with probability ≥ 3/5 -/
lemma alices_success (o : Oracle) (d t : ℕ) [Discrete o d] (m : (o.final t).prob true ≥ 2/3):
    (alices (alice o d t) (t+1)).pr (λ (p,y) ↦ p = o.probs y ∧ y.head) ≥ 3/5 := by
  simp only [Oracle.final, prob_bind, exp, prob_pure, @eq_comm _ true _] at m
  simp only [pr, exp]
  have sub : (o.fold (t+1)).supp.image (λ y ↦ (o.probs y,y)) ⊆ (alices (alice o d t) (t+1)).supp := by
    intro ⟨p,y⟩ m; simp only [Finset.mem_image, Prod.mk.injEq] at m
    rcases m with ⟨z,m,zp,zy⟩; simp only [mem_iff_pos, ←zp, zy] at m ⊢
    exact lt_of_lt_of_le (mul_pos (by norm_num) m) (alices_correct o d t y)
  refine' ge_trans (Finset.sum_le_sum_of_subset_of_nonneg sub _) _
  · intro ⟨p,y⟩ _ _; apply mul_nonneg (prob_nonneg _); split_ifs; norm_num; norm_num
  · rw [Finset.sum_image]; simp only [true_and, mul_ite, mul_one, mul_zero, ge_iff_le]
    · have le : ∀ y, 9/10 * (o.fold (t+1)).prob y * (if y.head then 1 else 0) ≤
          (if y.head then (alices (alice o d t) (t+1)).prob (o.probs y, y) else 0) := by
        intro y; by_cases yh : y.head
        · simp only [yh, if_true, mul_one]; apply alices_correct
        · simp only [yh, if_false, mul_zero, le_refl]
      refine le_trans ?_ (Finset.sum_le_sum (λ _ _ ↦ le _))
      simp only [mul_assoc, ←Finset.mul_sum]
      apply le_trans _ (mul_le_mul_of_nonneg_left m (by norm_num))
      norm_num
    · intro y _ z _; simp only [Prod.ext_iff]; exact And.right

/-- If Alice is correct and Bob rejects, the probability of false is ≤ 1/9 -/
lemma evil_bobs_lies' (o : Oracle) (d : ℕ) [Discrete o d] (eve : Bob) {n : ℕ} {p : Vector ℝ n} {y : Vector Bool n}
    (ac : p = o.probs y) : (bobs o d eve p y).cond (λ r ↦ r = some false) (λ r ↦ r.isSome) ≤ 1/9 := by
  induction' n with n h
  · simp only [bobs, cond_pure, if_false]; norm_num
  · simp only [o.probs_succ, Vector.eq_cons_iff] at ac
    apply le_trans (cond_bind_le_of_cut (λ r ↦ r.isSome)); apply max_le
    · refine' le_trans (cond_bind_le_first (λ r ↦ r = some false)
        (λ r ↦ r.isSome) (λ r ↦ r = some false) (λ r ↦ r.isSome) _ _) _;
      · intro r s pr ps r0 s0 _; match r with
        | none => simp only at r0 | some false => rfl
        | some true => simp only [s0, prob_pure, ite_false, ne_eq, not_true] at ps
      · intro r s pr ps ri; match r with
        | none => simp only at ri
        | some r => simp only [prob_pure, ite_one_zero_ne_zero] at ps; simp only [ps, Option.isSome]
      · exact h ac.2
    · refine' cond_bind_le_second (λ r ↦ r = some false) (λ r ↦ r.isSome)
        (λ r : Option Bool ↦ ¬r.isSome) (by norm_num) _
      intro r pr ri; match r with
      | some _ => simp only [Option.isSome] at ri
      | none =>
          simp only; apply cond_bind_le_of_forall_le (by norm_num)
          intro b _; match b with
          | true => simp only [if_true, bind_const, cond_pure, if_false]; norm_num
          | false =>
            simp only [if_false]; rw [cond_eq_pr]
            · refine' le_trans _ (vera_prob o d y.tail p.head)
              simp only [pr_bind, pr_pure]; apply exp_mono; intro r _
              simp only [ite_one_zero_congr, ac.1, decide_True]
              match r with
              | false => simp only [ite_true, le_refl]
              | true => simp only [ite_false, le_refl]
            · simp only [pr_eq_one, prob_bind]
              intro r h; match r with
              | some _ => simp only [Option.isSome]
              | none =>
                contrapose h; simp only [not_not]; apply exp_eq_zero
                intro x _; simp only [prob_pure, if_false]

/-- If Alice is good, the probability of false is ≤ 1/9 -/
lemma evil_bobs_lies (o : Oracle) (d t : ℕ) [Discrete o d] (eve : Bob) {p : Vector ℝ (t+1)} {y : Vector Bool (t+1)}
    (ac : p = o.probs y) (yt : y.head) : (bobs o d eve p y).pr (λ r ↦ extract ((p,y),r) = false) ≤ 1/9 := by
  rw [pr_eq_cond_add_cond (λ r : Option Bool ↦ r.isSome)]
  have b1 : (bobs o d eve p y).cond (λ r ↦ extract ((p,y),r) = false) (λ r ↦ ¬r.isSome) = 0 := by
    apply cond_eq_zero; intro r _ ri
    simp only [Option.not_isSome_iff_eq_none] at ri; simp only [ri, extract, yt]
  simp only [b1, zero_mul, add_zero]
  refine' le_trans (mul_le_of_le_one_right cond_nonneg pr_le_one) _
  refine' le_trans (le_of_eq _) (evil_bobs_lies' o d eve ac)
  apply cond_congr; intro r _ ri; match r with
  | some r => simp only [extract, Option.some_inj]
  | none => simp only at ri

/-- Alice wins the debate with probability ≥ 8/15 -/
theorem completeness' (o : Oracle) (d t : ℕ) [Discrete o d] (m : (o.final t).prob true ≥ 2/3) (eve : Bob) :
    (debate o d (alice o d t) eve t).prob true ≥ 8/15 := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ge_iff_le, ←pr_eq_prob]
  refine' le_trans (by norm_num) (le_pr_bind_of_cut _ (8/9) (alices_success o d t m) _ (by norm_num))
  intro ⟨p,y⟩ _ s; simp only [pr_map] at s ⊢
  have b : (bobs o d eve p y).pr (λ r ↦ ¬extract ((p,y),r) = true) ≤ 1/9 := by
    simp only [Bool.not_eq_true]; exact evil_bobs_lies _ _ _ _ s.1 s.2
  simp only [pr_neg] at b; linarith

-- Soundness.  We assume that
-- 1. Pr(final ≤ 1/3)
-- 2. Bob is honest.
-- 3. Alice is secretly Eve, and might be evil
-- Then we have
-- 1. If Alice ever lies, Bob can win w.p. ≥ 8/9
-- 2. If Alice is honest, she produces true w.p ≤ 1/3

/-- ∀ y, Evil Alice produces (p,y) with p correct with probability ≤ o.prob y -/
lemma evil_alices_correct (o : Oracle) (t : ℕ) (eve : Alice) (y : Vector Bool (t+1)) :
    (alices eve (t+1)).prob (o.probs y, y) ≤ (o.fold (t+1)).prob y := by
  suffices h : ∀ n z, (alices eve n).prob (o.probs z, z) ≤ (o.fold n).prob z by apply h
  intro n; induction' n with n h
  · intro y; simp only [alices, Oracle.probs, prob_pure, Prod.ext_iff, true_and, Oracle.fold,
      ite_le_ite_iff, imp_self]
  · intro y; simp only [alices, Oracle.fold, prob_bind]
    apply exp_le_exp_of_map (λ x ↦ x.2)
    · intro ⟨p0,y0⟩ ⟨p1,y1⟩ m0 m1 ye; simp only at ye
      have comm : ∀ x p d, x * @ite _ (o.probs y.tail = p) d (1:ℝ) 0 = @ite _ (o.probs y.tail = p) d 1 0 * x := by
        intro _ _ _; apply mul_comm
      simp only [←ye, Prod.mk.injEq, and_true, prob_pure, Vector.eq_cons_iff, Oracle.probs,
        Vector.head_cons, Vector.tail_cons, mul_ne_zero_iff, ite_and_one_zero,
        comm, mul_assoc, exp_const_mul, mul_ne_zero_iff, ite_one_zero_ne_zero] at m0 m1 ⊢
      rw [←m0.2.1, ←m1.2.1]
    · intro ⟨p,x⟩ _
      simp only [prob_pure, Prod.ext_iff, Oracle.probs, Vector.eq_cons_iff, Vector.head_cons,
        Vector.tail_cons, ite_and_one_zero, exp_const_mul]
      by_cases yp : o.probs y.tail = p
      · simp only [yp, if_true, one_mul, mul_one]; simp only [←yp]
        by_cases yx : y.tail = x
        · simp only [←yx, if_true, mul_one]
          apply mul_le_mul (h _) _ _ (prob_nonneg _)
          · apply exp_le_of_forall_le; intro q _;
            by_cases oq : (o y.tail.toList).prob true = q
            · simp only [oq, if_true, one_mul]
              simp only [←oq, ←eq_bernoulli, le_refl]
            · simp only [oq, if_false, zero_mul]; apply exp_nonneg; intro _ _; exact ite_one_zero_nonneg
          · apply exp_nonneg; intro _ _; apply mul_nonneg; exact ite_one_zero_nonneg
            apply exp_nonneg; intro _ _; exact ite_one_zero_nonneg
        · simp only [yx, if_false, mul_zero, exp_const, le_refl]
      · simp only [yp, if_false, mul_zero, zero_mul, exp_const]
        apply mul_nonneg (prob_nonneg _); apply exp_nonneg; intro _ _
        exact mul_nonneg ite_one_zero_nonneg ite_one_zero_nonneg
    · intro _ _; apply exp_nonneg; intro _ _; exact (prob_nonneg _)

/-- Evil Alice produces a p-correct true trace with probability ≤ 1/3 -/
lemma evil_alices_lies (o : Oracle) (t : ℕ) (eve : Alice) (m : (o.final t).prob true ≤ 1/3) :
    (alices eve (t+1)).pr (λ (p,y) ↦ p = o.probs y ∧ y.head) ≤ 1/3 := by
  refine' le_trans _ m
  simp only [pr, Oracle.final, prob_bind]
  apply exp_le_exp_of_map (λ x ↦ x.2)
  · intro ⟨p0,y0⟩ ⟨p1,y1⟩ m0 m1 ye; simp only at ye
    simp only [←ye, mul_ne_zero_iff, ite_and_one_zero, ite_one_zero_ne_zero] at m0 m1
    simp only [←ye, Prod.ext_iff, and_true, m0.2.1, m1.2.1]
  · intro ⟨p,y⟩ h; simp only [prob_pure, mul_ne_zero_iff, ite_one_zero_ne_zero] at h ⊢
    simp only [h.2.1, h.2.2, if_true, mul_one]
    apply evil_alices_correct
  · intro _ _; exact prob_nonneg _

/-- If Alice has correct probabilities, Bob rarely rejects -/
lemma bobs_accepts (o : Oracle) (d t : ℕ) [Discrete o d] {n : ℕ} {p : Vector ℝ n} {y : Vector Bool n}
    (ac : p = o.probs y) : (1 - 1/10/(↑t+1) : ℝ) ^ n ≤ (bobs o d (bob o d t) p y).pr (λ r ↦ r = none) := by
  induction' n with n h
  · simp only [bobs, pr_pure, if_true, pow_zero, le_refl]
  · simp only [Oracle.probs, Vector.eq_cons_iff] at ac
    refine' le_trans (le_of_eq (pow_succ' _ _))
      (le_pr_bind_of_cut _ _ (h ac.2) _ (le_of_lt alice_sub_div_pos))
    intro r _ r0; simp only [r0]
    refine' le_trans (le_of_eq (mul_one _).symm)
      (@le_pr_bind_of_cut _ _ _ _ _ (λ b ↦ b = true) _ 1 _ _ zero_le_one)
    · have b := bob_prob o d t y.tail p.head
      simp only [ac, Nat.succ_sub_one, decide_True, Bool.not_eq_true, pr_eq_prob] at b
      simp only [←ac.1] at b
      simp only [pr_eq_prob, bool_prob_true_of_false, sub_le_sub_iff_left, div_div]
      exact b
    · intro b _ b1; simp only [b1, if_true, bind_const, pr_pure, le_refl]

/-- If Alice lies about probabilities, Bob succeeds in catching Alice in a lie with probability ≥ 4/5 -/
lemma bobs_catches (o : Oracle) (d t : ℕ) [Discrete o d] {p : Vector ℝ (t+1)} {y : Vector Bool (t+1)}
    (ac : p ≠ o.probs y) : 4/5 ≤ (bobs o d (bob o d t) p y).pr (λ r ↦ r = some false) := by
  suffices h : ∀ n (p : Vector ℝ n) (y : Vector Bool n), p ≠ o.probs y →
      8/9 * (1 - 1/10/(t+1) : ℝ) ^ n ≤ (bobs o d (bob o d t) p y).pr (λ r ↦ r = some false) by
    refine' le_trans _ (h _ p y ac)
    exact le_trans (by norm_num) (mul_le_mul_of_nonneg_left le_alice_pow (by norm_num))
  intro n p y ac; induction' n with n h'
  · simp only [Vector.eq_nil] at ac
  · by_cases act : p.tail = o.probs y.tail
    · simp only [Oracle.probs, Vector.ne_cons_iff, act, Ne.def, eq_self_iff_true, or_false] at ac
      simp only [bobs, ge_iff_le]
      refine' le_trans _ (le_pr_bind_of_cut _ (8/9 * (1 - 1/10/(↑t+1))) (bobs_accepts o d t act) _ _)
      · rw [←mul_assoc, mul_comm _ (8/9), mul_assoc]
        refine' mul_le_mul_of_nonneg_left (le_of_eq _) (by norm_num)
        simp only [←Nat.cast_add_one, Nat.add_sub_cancel, pow_succ']
      · intro r _ r0; simp only [r0]; rw [mul_comm]
        refine' le_pr_bind_of_cut (1 - 1/10/(↑t+1)) (8/9) _ _ (by norm_num)
        · exact λ b ↦ ¬b
        · have b := bob_prob o d t y.tail p.head
          simp only [ac, Nat.succ_sub_one, decide_False, Bool.not_eq_false, pr_eq_prob] at b
          simp only [Bool.not_eq_true, pr_eq_prob, bool_prob_false_of_true, Nat.succ_sub_one,
            sub_le_sub_iff_left, div_div, b]
        · intro b _ e; simp only [Bool.not_eq_true] at e
          have v := vera_prob o d y.tail p.head
          simp only [ac, decide_False, ne_eq, Bool.not_eq_false, pr_eq_prob] at v
          simp only [e, if_false, pr_bind, pr_pure, Option.some_inj, exp_eq_prob, bool_prob_false_of_true]
          linarith
      · exact mul_nonneg (by norm_num) (le_of_lt alice_sub_div_pos)
    · refine' le_trans _ (le_pr_bind_of_cut _ 1 (h' p.tail y.tail act) _ zero_le_one)
      · simp only [Nat.succ_sub_one, mul_one]
        refine' mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_of_le_one (le_of_lt alice_sub_div_pos) (le_of_lt alice_sub_div_lt_one) (Nat.le_succ _)
      · intro r _ e; refine' le_of_eq (Eq.symm _); rw [pr_eq_one]; intro s
        simp only [e, prob_pure, ite_one_zero_ne_zero]; exact λ e ↦ e

/-- Bob wins the debate with probability ≥ 8/15 -/
theorem soundness' (o : Oracle) (d t : ℕ) [Discrete o d] (m : (o.final t).prob true ≤ 1/3) (eve : Alice) :
    (debate o d eve (bob o d t) t).prob false ≥ 8/15 := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ge_iff_le, ←pr_eq_prob]
  have a := evil_alices_lies o t eve m
  rw [pr_neg', sub_le_iff_le_add, add_comm, ←sub_le_iff_le_add] at a
  refine' le_trans (by norm_num) (le_pr_bind_of_cut _ (4/5) a _ (by norm_num))
  intro (p,y) _ g; simp only [not_and_or] at g
  by_cases ac : p = o.probs y
  · simp only [ac, false_or, Bool.not_eq_true] at g; simp only [pr_map]
    refine' le_trans (le_trans _ (bobs_accepts o d t ac)) (pr_mono _)
    · exact le_trans (by norm_num) le_alice_pow
    · intro r _ e; simp only [e, extract, g]
  · simp only [pr_map]; refine' le_trans (bobs_catches o d t ac) (pr_mono _)
    intro r _ e; simp only [e, extract]
