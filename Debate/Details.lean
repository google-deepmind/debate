import Comp.Basic
import Debate.Protocol
import Prob.Arith
import Prob.Chernoff
import Prob.Cond
import Misc.Finset
import Misc.If

/-!
# Correctness of the stochastic oracle doubly-efficient debate algorithm (details)

See `Correct.lean` for the summary.
-/

open Classical
open Prob
open Option (some none)
open Real (log)
open Set
open scoped Real
noncomputable section

variable {i : OracleId}
variable {o : Oracle}
variable {n t : ℕ}
variable {k c s b e p q v : ℝ}

/-!
## Correctness of Alice, Bob, and Vera

We first show that Honest Alice, Bob, and Vera do their jobs correctly to
within the necessary failure probabilities.
-/

/-- samples' is samples without the Nat.ceil -/
def samples' (e q : ℝ) : ℝ := -Real.log (q/2) / (2 * e^2)
lemma le_samples (e q : ℝ) : samples' e q ≤ samples e q := Nat.le_ceil _

/-- Honest Alice has error ≥ e with probability ≤ q -/
lemma alice_pr_le (o : Oracle) (i : OracleId) (e0 : 0 < e) (q0 : 0 < q) (y : Vector Bool n) :
    ((alice' e q i _ y).prob' o).pr (λ p ↦ e ≤ |p - (o _ y).prob true|) ≤ q := by
  simp only [alice', Comp.prob', Comp.prob_estimate, Comp.prob_query]
  refine le_trans (chernoff_estimate_abs_le (o _ y) (samples e q) (le_of_lt e0)) ?_
  have le : -2 * ↑(samples e q) * e^2 ≤ -2 * samples' e q * e^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left (le_samples _ _) (by norm_num))
      (sq_nonneg _)
  refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr le) (by norm_num)) ?_; clear le
  simp only [samples', div_eq_inv_mul, ←mul_assoc, mul_inv]; norm_num
  simp only [mul_comm _ (e^2), ←mul_assoc, mul_inv_cancel (pow_ne_zero _ (ne_of_gt e0)), one_mul]
  rw [Real.exp_log]; ring_nf; rfl; positivity

/-- Honest Alice has error ≤ e with probability ≥ 1 - q
    < e is also true, but annoying to work with later. -/
lemma le_alice_pr (o : Oracle) (i : OracleId) (e0 : 0 < e) (q0 : 0 < q) (y : Vector Bool n) :
    1 - q ≤ ((alice' e q i _ y).prob' o).pr (λ p ↦ |p - (o _ y).prob true| ≤ e) := by
  trans ((alice' e q i _ y).prob' o).pr (λ p ↦ |p - (o _ y).prob true| < e)
  · rw [pr_neg']; simp only [not_lt]; linarith [alice_pr_le o i e0 q0 y]
  · apply pr_mono; intro _ _ h; exact le_of_lt h

/-- Honest Bob usually accepts if Alice is off by ≤ c -/
lemma bob_complete (o : Oracle) (i : OracleId) (cs : c < s) (q0 : 0 < q) {y : Vector Bool n}
    (good : |p - (o _ y).prob true| ≤ c) :
    ((bob' c s q i _ y p).prob' o).prob false ≤ q := by
  simp only [bob', prob_bind, prob_pure, false_eq_decide_iff, not_lt, Comp.prob',
    Comp.prob_bind, Comp.prob_pure]
  rw [←pr]
  refine le_trans (pr_mono ?_) (alice_pr_le o i (by linarith) q0 y)
  intro b _ h; generalize hx : (o _ y).prob true = x; rw [hx] at good; clear hx
  have e : b - x = -((p - b) - (p - x)) := by abel
  rw [e, abs_neg]; refine le_trans ?_ (abs_sub_abs_le_abs_sub _ _)
  calc (s - c) / 2
    _ ≤ (c + s) / 2 - c := by linarith
    _ ≤ |p - b| - |p - x| := sub_le_sub h good

/-- Honest Bob usually rejects if Alice is off by ≥ s -/
lemma bob_sound (o : Oracle) (i : OracleId) (cs : c < s) (q0 : 0 < q) {y : Vector Bool n}
    (bad : |p - (o _ y).prob true| ≥ s) :
    ((bob' c s q i _ y p).prob' o).prob true ≤ q := by
  simp only [bob', prob_bind, prob_pure, true_eq_decide_iff, not_lt, Comp.prob',
    Comp.prob_bind, Comp.prob_pure]
  rw [←pr]
  refine le_trans (pr_mono ?_) (alice_pr_le o i (by linarith) q0 y)
  intro b _ h; generalize hx : (o _ y).prob true = x; rw [hx] at bad; clear hx
  have e : b - x = (p - x) - (p - b) := by abel
  rw [e]; refine le_trans ?_ (abs_sub_abs_le_abs_sub _ _)
  calc (s - c) / 2
    _ ≤ s - (c + s) / 2 := by linarith
    _ ≤ |p - x| - |p - b| := sub_le_sub bad (le_of_lt h)

/-!
## Transposed protocol with Alice moving first, then Bob

As written the debate protocol is awkward to analyze, since Alice's and Bob's moves are
interleaved and intermediate states are discarded.  Therefore, we rewrite it into a
form where Alice moves first, then Bob moves.
-/

/-- All of Alice's moves, and the resulting trace -/
def alices (o : Oracle) (alice : Alice) : (n : ℕ) → Prob (Vector ℝ n × Vector Bool n)
| 0 => pure (Vector.nil, Vector.nil)
| n+1 => do
  let (p,y) ← alices o alice n
  let q ← (alice _ y).prob' o
  let x ← bernoulli q
  return (q ::ᵥ p, x ::ᵥ y)

/-- All of Bob's moves, after Alice's -/
def bobs (o : Oracle) (bob : Bob) (vera : Vera) {n : ℕ} (p : Vector ℝ n) (y : Vector Bool n) :
    Prob (Option Bool) :=
  match n with
  | 0 => pure none
  | _+1 => do match ←bobs o bob vera p.tail y.tail with
    | some r => return r
    | none => do
      let b ← (bob _ y.tail p.head).prob' o
      let v ← (vera _ y.tail p.head).prob' o
      return if b then none else some v

/-- All of Alice's moves prior to Bob's, producing the full trace -/
def trace (o : Oracle) (alice : Alice) (bob : Bob) (vera : Vera) (t : ℕ) :
    Prob ((Vector ℝ (t+1) × Vector Bool (t+1)) × Option Bool) := do
  let a ← alices o alice (t+1)
  Prod.mk a <$> bobs o bob vera a.1 a.2

/-- Extract the final result -/
def extract (x : (Vector ℝ (t+1) × Vector Bool (t+1)) × Option Bool) : Bool := match x.2 with
  | none => x.1.2.head
  | some r => r

/-- debate, with all of Alice's moves prior to Bob's, and producing the full trace -/
def transposed (o : Oracle) (alice : Alice) (bob : Bob) (vera : Vera) (t : ℕ) : Prob Bool :=
  extract <$> trace o alice bob vera t

/-- Shim to turn alices >>= bobs into steps -/
def shim {n : ℕ} (y : Vector Bool n) : Option Bool → State n
| some r => .error r
| none => .ok y

/-- The transposed formulation of debate is the same -/
lemma debate_eq_transposed (o : Oracle) (alice : Alice) (bob : Bob) (vera : Vera) (t : ℕ) :
    (debate alice bob vera t).prob' o = transposed o alice bob vera t := by
  have h : ∀ n, (steps alice bob vera n).prob (fun _ ↦ o) =
      alices o alice n >>= λ (p,y) ↦ shim y <$> bobs o bob vera p y := by
    intro n; induction' n with n h
    · simp only [steps, alices, pure_bind, bobs, shim, map_eq, Comp.prob', Comp.prob_pure]
    · simp only [steps, h, alices, bobs, bind_assoc, Comp.prob', Comp.prob_bind]
      apply congr_arg₂ _ rfl; funext ⟨p,y⟩
      simp only [pure_bind, map_eq, bind_assoc, Vector.tail_cons, Vector.head_cons,
        bind_comm _ (bobs _ _ _ _ _)]
      apply congr_arg₂ _ rfl; funext r; match r with
      | some r => simp only [shim, pure_bind, bind_pure, bind_const, Comp.prob_pure]
      | none =>
        simp only [shim, step, Comp.prob_bind, Comp.prob_allow_all]
        apply congr_arg₂ _ rfl; funext q
        simp only [bind_assoc, bind_comm _ ((bob _ _ _).prob _)]; apply congr_arg₂ _ rfl; funext s
        match s with
        | true =>
          simp only [if_true, Comp.prob_bind, Comp.prob_pure, Comp.prob_sample', bind_assoc]
          apply congr_arg₂ _ rfl; funext x; simp only [bind_const, pure_bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Comp.prob_bind, Comp.prob_allow_all,
            Comp.prob_pure, Nat.add_succ_sub_one, Nat.add_zero, bind_assoc, pure_bind, bind_const]
  simp only [debate, transposed, trace, extract, h, bind_assoc, map_eq, Comp.prob', Comp.prob_bind]
  apply congr_arg₂ _ rfl; funext ⟨p,y⟩; apply congr_arg₂ _ rfl; funext r; match r with
  | some true => simp only [shim, pure_bind, Option.getD, Comp.prob_pure]
  | some false => simp only [shim, pure_bind, Option.getD, Comp.prob_pure]
  | none => simp only [shim, pure_bind, Option.getD, Comp.prob_pure]

/-!
# Close probabilities

We define closeness of probability vectors to match Oracle dist, and a snapping operation
that turns any Alice into an always close Alice.  For close Alices, snap changes probabilities
only moderately.
-/

/-- The exact probabilities given a trace -/
def Oracle.probs (o : Oracle) {n : ℕ} (y : Vector Bool n) : Vector ℝ n := match n with
| 0 => Vector.nil
| _+1 => (o _ y.tail).prob true ::ᵥ o.probs y.tail
lemma Oracle.probs_succ (o : Oracle) {n : ℕ} {y : Vector Bool (n+1)} :
    o.probs y = (o n y.tail).prob true ::ᵥ o.probs y.tail := rfl

/-- Closeness for two probability vectors -/
def close (x y : Vector ℝ n) (e : ℝ) : Prop := ∀ i, |x.get i - y.get i| ≤ e
lemma close_nil {x y : Vector ℝ 0} (e : ℝ) : close x y e := by simp only [close, IsEmpty.forall_iff]
lemma close_cons {p q : ℝ} {x y : Vector ℝ n} {e : ℝ} :
    close (p ::ᵥ x) (q ::ᵥ y) e = (|p - q| ≤ e ∧ close x y e) := by
  simp only [close, Fin.forall_fin_succ, Vector.get_zero, Vector.head_cons, Vector.get_cons_succ,
    and_true]
lemma close_succ {x y : Vector ℝ (n+1)} {e : ℝ} :
    close x y e = (|x.head - y.head| ≤ e ∧ close x.tail y.tail e) := by
  convert @close_cons n x.head y.head x.tail y.tail e; repeat simp only [Vector.cons_head_tail]
lemma close_mono {x y : Vector ℝ n} (xy : close x y c) (cs : c ≤ s) : close x y s := by
  simp only [close] at xy ⊢; intro i; exact le_trans (xy i) cs

/-- (o.fold (n+1)).prob y decomposes as a product -/
lemma Oracle.fold_succ_prob (o : Oracle) {n : ℕ} (y : Vector Bool (n+1)) :
    (o.fold (n+1)).prob y = (o.fold n).prob y.tail * (o _ y.tail).prob y.head := by
  simp only [Oracle.fold, prob_bind, prob_pure, Vector.eq_cons_iff, ite_and_one_zero, exp_mul_const,
    @eq_comm _ y.head]
  rw [←exp_eq_prob, ←exp_mul_const]; apply exp_congr'
  · intro x; by_cases yx : y.tail = x
    · simp only [yx, if_true, mul_one, one_mul]; apply congr_arg₂ _ rfl; apply exp_eq_prob
    · simp only [yx, if_false, mul_zero]; split_ifs with h; simp [h] at yx; simp [h]
  · intro _; exact Classical.dec _

/-- Snap an Alice into a close oracle -/
def snap (o : Oracle) (alice : Alice) (e : ℝ) : Oracle := λ _ y ↦ do
  let p ← (alice _ y).prob' o
  let q := (o _ y).prob true
  let p := if |p - q| ≤ e then p else q
  bernoulli p

/-- Snap produces a close oracle -/
lemma snap_dist (alice : Alice) (e0 : 0 < e) : dist o (snap o alice e) ≤ e := by
  simp only [dist]; apply csSup_le (Set.range_nonempty _); intro p
  simp only [mem_range, forall_exists_index]; intro n h; rw [←h]; clear h
  apply csSup_le (Set.range_nonempty _); intro d h
  simp only [mem_range] at h; rcases h with ⟨y,h⟩; rw [←h]; clear h
  simp only [snap, prob_bind, abs_le]; constructor
  · rw [le_sub_iff_add_le, add_comm, ←sub_eq_add_neg, sub_le_iff_le_add]
    apply exp_le_of_forall_le; intro q _; simp only [bernoulli_prob_true']
    apply max_le (add_nonneg (prob_nonneg _) (le_of_lt e0)); apply min_le_of_right_le
    split_ifs with h; linarith [h.1]; linarith
  · rw [sub_le_iff_le_add, add_comm, ←sub_le_iff_le_add]
    apply le_exp_of_forall_le; intro q _; simp only [bernoulli_prob_true']
    apply le_max_of_le_right; apply le_min; linarith [prob_le_one (o _ y) true]
    split_ifs with h; linarith; linarith

/-- All of Alice's moves, but with probabilities snapped to close when sampling -/
def snaps (o : Oracle) (alice : Alice) (e : ℝ) : (n : ℕ) → Prob (Vector ℝ n × Vector Bool n)
| 0 => pure (Vector.nil, Vector.nil)
| n+1 => do
  let (p,y) ← snaps o alice e n
  let q ← (alice _ y).prob' o
  let c := (o _ y).prob true
  let x ← bernoulli (if |q - c| ≤ e then q else c)
  return (q ::ᵥ p, x ::ᵥ y)

/-- Snapping doesn't changed prob for close p -/
lemma snaps_prob (alice : Alice) {p : Vector ℝ n} {y : Vector Bool n} (c : close p (o.probs y) e) :
    (snaps o alice e n).prob (p,y) = (alices o alice n).prob (p,y) := by
  induction' n with n h
  · simp only [alices, snaps]
  · simp only [alices, snaps, prob_bind, prob_pure, Prod.ext_iff, Vector.eq_cons_iff]
    apply exp_congr'; intro (q,z)
    by_cases pq : p.tail = q
    · by_cases yz : y.tail = z
      · simp only [close_succ, pq, yz, Oracle.probs_succ, Vector.head_cons, Vector.tail_cons] at c
        simp only [h c.2]; apply congr_arg₂ _ rfl
        apply exp_congr; intro r _; by_cases pr : p.head = r
        · simp only [pr] at c
          simp only [pr, pq, yz, c.1, true_and, and_true, if_true]
        · simp only [pr, false_and, if_false, exp_const]
      · simp only [yz, and_false, if_false, exp_const, mul_zero]
    · simp only [pq, and_false, false_and, if_false, exp_const, mul_zero]

/-- Final result of snaps -/
def final (x : Vector ℝ (t+1) × Vector Bool (t+1)) : Bool := x.2.head

/-- As an oracle, snaps looks like snap (fold version) -/
lemma snaps_eq_snap_fold (alice : Alice) (n : ℕ) :
    Prod.snd <$> snaps o alice e n = (snap o alice e).fold n := by
  induction' n with n h
  · simp only [snaps, map_pure, Oracle.fold]
  · simp only [snaps, Oracle.fold, map_bind, map_pure, ←h, map_eq, bind_assoc]
    apply congr_arg₂ _ rfl; ext ⟨p,y⟩
    simp only [pure_bind, snap, bind_assoc]

/-- As an oracle, snaps looks like snap (final version) -/
lemma snaps_eq_snap_final (alice : Alice) (t : ℕ) :
    final <$> snaps o alice e (t+1) = (snap o alice e).final t := by
  simp only [final, Oracle.final, ←snaps_eq_snap_fold, map_eq, bind_assoc, pure_bind]

/-!
# Completeness

We assume that
1. The oracle is k-Lipschitz
2. Alice is honest
3. Bob is secretly Eve, and might be evil

Then we have
1. Alice usually gives close probabilities at all steps.
2. When Alice is always close, she is effectively a close oracle,
   so with good probability she produces close probability with final = true.
3. If Alice is close and final = true, Bob has to reject, but Vera usually yells.

We prove all intermediate theorems with flexible constants, then pick at the end.
-/

/-- Alice produces (p,y) with p close to o.probs y with good probability -/
lemma alices_close (o : Oracle) (e0 : 0 < e) (q0 : 0 < q) (q1 : q ≤ 1) (n : ℕ) :
    (1 - q : ℝ)^n ≤ (alices o (alice e q) n).pr (fun (p,y) ↦ close p (o.probs y) e) := by
  induction' n with n h
  · simp only [Nat.zero_eq, pow_zero, alices, close_nil, pr_pure, if_true, le_refl]
  · simp only [pow_succ, alices, Oracle.probs, pr_bind, pr_pure, Vector.tail_cons, close_cons,
      ite_and_one_zero, exp_const_mul, exp_const, exp_mul_const]
    apply le_exp_of_cut (fun (p,y) ↦ close p (o.probs y) e) ((1 - q)^n) (1 - q)
    · apply h
    · intro (p,y) _ c; simp only at c; simp only [c, if_true, mul_one]
      exact le_alice_pr o _ e0 q0 y
    · intro _ _ _; apply mul_nonneg; apply exp_nonneg; intro _ _; repeat apply ite_one_zero_nonneg
    · linarith

/-- Alice produces (p,y) with p close and y true with good probability, since if we condition on
    Alice being close she does as least as well as a close oracle. -/
lemma alices_success (o : Oracle) (L : o.lipschitz t k) (e0 : 0 < e) (q0 : 0 < q) (q1 : q ≤ 1) :
    (o.final t).prob true - k * e - ((1:ℝ) - (1 - q : ℝ)^(t+1)) ≤
      (alices o (alice e q) (t+1)).pr (fun (p,y) => close p (o.probs y) e ∧ y.head) := by
  trans (snaps o (alice e q) e (t+1)).pr (fun (_,y) => y.head) - (1 - (1 - q)^(t+1))
  · apply sub_le_sub_right; trans ((snap o (alice e q) e).final t).prob true
    · have lip := (abs_le.mp (L.le (snap o (alice e q) e))).2
      simp only [sub_le_iff_le_add, add_comm _ (k * e)] at lip ⊢
      exact le_trans lip (add_le_add_right (mul_le_mul_of_nonneg_left (snap_dist _ e0) L.k0) _)
    · apply le_of_eq; simp only [←snaps_eq_snap_final, prob_map]
      apply pr_congr; intro _ _; rfl
  · simp only [sub_le_iff_le_add]
    rw [pr_eq_add_of_cut (fun (p,y) => close p (o.probs y) e)]; apply add_le_add
    · simp only [pr]; apply exp_mono'; intro (p,y)
      by_cases c : close p (o.probs y) e
      · simp only [c, true_and, if_false, add_zero, snaps_prob _ c, and_true, le_refl]
      · simp only [c, false_and, if_false, zero_add, if_true, mul_one, and_false, mul_zero, le_refl]
    · trans (snaps o (alice e q) e (t+1)).pr (fun (p,y) => ¬close p (o.probs y) e)
      · apply pr_mono; intro _ _; simp only [and_imp, imp_self, implies_true]
      · have ae : (snaps o (alice e q) e (t+1)).pr (fun (p,y) => close p (o.probs y) e) =
            (alices o (alice e q) (t+1)).pr (fun (p,y) => close p (o.probs y) e) := by
          apply exp_congr'; intro (p,y)
          by_cases c : close p (o.probs y) e
          · simp only [c, if_true, mul_one, snaps_prob _ c]
          · simp only [c, if_false, mul_zero]
        simp only [pr_neg, ae]; linarith [alices_close o e0 q0 q1 (t+1)]

/-- If Alice is correct and Bob rejects, the probability of false is low -/
lemma evil_bobs_lies' (o : Oracle) (eve : Bob) (cs : c < s) (v0 : 0 < v)
    {p : Vector ℝ n} {y : Vector Bool n} (py : close p (o.probs y) c) :
    (bobs o eve (vera c s v) p y).cond (λ r ↦ r = some false) (λ r ↦ r.isSome) ≤ v := by
  have v0' := le_of_lt v0
  induction' n with n h
  · simp only [bobs, cond_pure, Option.isSome_none, Bool.false_eq_true, and_self, ↓reduceIte, v0']
  · simp only [close_succ, Vector.eq_cons_iff] at py
    apply le_trans (cond_bind_le_of_cut (λ r ↦ r.isSome)); apply max_le
    · refine le_trans (cond_bind_le_first (λ r ↦ r = some false)
        (λ r ↦ r.isSome) (λ r ↦ r = some false) (λ r ↦ r.isSome) ?_ ?_) ?_;
      · intro r s pr ps r0 s0 _; match r with
        | none => simp only [Option.isSome_none, Bool.false_eq_true] at r0
        | some false => rfl
        | some true =>
          simp only [s0, prob_pure, some.injEq, Bool.false_eq_true, ↓reduceIte, ne_eq,
            not_true_eq_false] at ps
      · intro r s pr ps ri; match r with
        | none => simp only [Option.isSome_none, Bool.false_eq_true] at ri
        | some r => simp only [prob_pure, ite_one_zero_ne_zero] at ps; simp only [ps, Option.isSome]
      · exact h py.2
    · refine cond_bind_le_second (λ r ↦ r = some false) (λ r ↦ r.isSome)
        (λ r : Option Bool ↦ ¬r.isSome) v0' ?_
      intro r pr ri; match r with
      | some _ => simp only [Option.isSome, not_true_eq_false] at ri
      | none =>
          simp only; apply cond_bind_le_of_forall_le v0'
          intro b _; match b with
          | true => simp [cond_pure, v0']
          | false =>
            simp only [if_false]; rw [cond_eq_pr]
            · refine le_trans ?_ (bob_complete o VeraId cs v0 py.1)
              simp only [pr_bind, pr_pure, Option.some_inj, exp_eq_prob]; rfl
            · simp only [pr_eq_one, prob_bind]
              intro r h; match r with
              | some _ => simp only [Option.isSome]
              | none =>
                contrapose h; clear h; simp only [not_not]; apply exp_eq_zero
                intro x _; simp only [prob_pure, if_false]

/-- If Alice is good, the probability of false is low -/
lemma evil_bobs_lies (o : Oracle) (eve : Bob) (cs : c < s) (v0 : 0 < v)
    {p : Vector ℝ (t+1)} {y : Vector Bool (t+1)} (py : close p (o.probs y) c) (yt : y.head) :
    (bobs o eve (vera c s v) p y).pr (λ r ↦ extract ((p,y),r) = false) ≤ v := by
  rw [pr_eq_cond_add_cond (λ r : Option Bool ↦ r.isSome)]
  have b1 : (bobs o eve (vera c s v) p y).cond (λ r ↦ extract ((p,y),r) = false)
      (λ r ↦ ¬r.isSome) = 0 := by
    apply cond_eq_zero; intro r _ ri
    simp only [Option.not_isSome_iff_eq_none] at ri
    simp [ri, extract, yt]
  simp only [b1, zero_mul, add_zero]
  refine le_trans (mul_le_of_le_one_right cond_nonneg pr_le_one) ?_
  refine le_trans (le_of_eq ?_) (evil_bobs_lies' o eve cs v0 py)
  apply cond_congr; intro r _ ri; match r with
  | some r => simp only [extract, Option.some_inj]
  | none => simp at ri

/-- Alice wins the debate with good probability -/
theorem completeness' (o : Oracle) (L : o.lipschitz t k) (eve : Bob)
    (c0 : 0 < c) (cs : c < s) (q0 : 0 < q) (q1 : q ≤ 1) (v0 : 0 < v) (v1 : v ≤ 1) :
    (1 - v) * ((o.final t).prob true - k * c - (1 - (1 - q) ^ (t + 1))) ≤
      ((debate (alice c q) eve (vera c s v) t).prob' o).prob true := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ge_iff_le, ←pr_eq_prob]
  refine le_trans ?_ (le_pr_bind_of_cut _ (1-v) (alices_success o L c0 q0 q1) ?_ ?_)
  · simp only [mul_comm _ (1-v), pr_eq_prob, le_refl]
  · intro ⟨p,y⟩ _ h; simp only [pr_map] at h ⊢
    have b : (bobs o eve (vera c s v) p y).pr (λ r ↦ ¬extract ((p,y),r) = true) ≤ v := by
      simp only [Bool.not_eq_true]; apply evil_bobs_lies o eve cs v0 h.1 h.2
    simp only [pr_neg] at b; linarith
  · linarith

/-
# Soudness

We assume that
1. The oracle is k-Lipschitz
2. Bob is honest
3. Alice is secretly Eve, and might be evil

Then we have
1. Alice can't raise the probability of success too much with close p, by Lipschitz.
2. If Alice gives close p, Bob rarely rejects.
3. If Alice is ever not close, Bob usually rejects, and Vera agrees.

For soundness, the threshold for close is s > c, where c is the smaller threshold
for closeness during completeness.
-/

/-- Evil Alice produces a close true trace with low probability, since by remaining close
    she looks like a close oracle. -/
lemma evil_alices_lies (o : Oracle) (L : o.lipschitz t k) (eve : Alice) (e0 : 0 < e) :
    (alices o eve (t+1)).pr (λ (p,y) ↦ close p (o.probs y) e ∧ y.head) ≤
      (o.final t).prob true + k * e := by
  trans (snaps o eve e (t+1)).pr (λ (p,y) ↦ close p (o.probs y) e ∧ y.head)
  · apply le_of_eq; apply exp_congr'; intro (p,y); by_cases c : close p (o.probs y) e
    · simp only [c, true_and, snaps_prob _ c]
    · simp only [c, false_and, if_false, mul_zero]
  · trans ((snap o eve e).final t).prob true
    · simp only [←snaps_eq_snap_final, prob_map]
      apply pr_mono; intro (p,y) _; simp only [final, and_imp, imp_self, implies_true]
    · have lip := (abs_le.mp (L.le (snap o eve e))).1
      rw [le_sub_iff_add_le, add_comm, ←sub_eq_add_neg, sub_le_iff_le_add] at lip
      exact le_trans lip (add_le_add_left (mul_le_mul_of_nonneg_left (snap_dist _ e0) L.k0) _)

/-- A score to take into account Vera's failure probability if Bob rejects -/
def vera_score (v : ℝ) : Option Bool → ℝ
| none => 1 - v
| some false => 1
| some true => 0

/-- Option Bool's univ-/
lemma option_bool_univ : (Finset.univ : Finset (Option Bool)) = {some true, some false, none} := by
  decide

/-- If Honest Bob rejects, Vera usually complains.  The error probability is higher if Bob
    does complain, though, so we use an expectation over vera_score. -/
lemma bobs_safe (o : Oracle) (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1)
    (qv : q ≤ v) (p : Vector ℝ n) (y : Vector Bool n) :
    (1 - v) * (1 - q) ^ n ≤ (bobs o (bob s b q) (vera c s v) p y).exp (vera_score v) := by
  induction' n with n h
  · simp only [Nat.zero_eq, pow_zero, mul_one, bobs, vera_score, exp_pure, le_refl]
  · simp only [bobs, exp_bind]; specialize h p.tail y.tail
    simp only [@exp_fintype (Option Bool), option_bool_univ, vera_score, Finset.mem_insert,
      some.injEq, Bool.true_eq_false, Finset.mem_singleton, or_self, not_false_eq_true,
      Finset.sum_insert, mul_zero, mul_one, Finset.sum_singleton, zero_add, Nat.succ_sub_one,
      Comp.prob', prob_pure, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, prob_bind] at h ⊢
    generalize hbs : bobs o (bob s b q) (vera c s v) p.tail y.tail = bs
    simp only [hbs] at h
    generalize hbn : (bob s b q n y.tail p.head).prob' o = bn
    trans (bs.prob (some false) + bs.prob none * (1 - v)) * (1 - q)
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right h (by linarith))
      rw [mul_assoc, ←pow_succ]
    · simp only [add_mul]; apply add_le_add
      · exact mul_le_of_le_one_right (prob_nonneg _) (by linarith)
      · rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (prob_nonneg _)
        trans bn.exp (fun r ↦ ((vera c s v _ y.tail p.head).prob' o).exp (fun x ↦
          (if some false = if r then none else some x then 1 else 0) +
          (if none = if r then none else some x then 1 else 0) * (1 - v)))
        · by_cases ps : |p.head - (o _ y.tail).prob true| ≤ s
          · rw [mul_comm]
            refine le_exp_of_cut (fun x ↦ x = true) (1-q) (1-v) ?_ ?_ ?_ (by linarith)
            · have bc := bob_complete o BobId sb q0 ps
              simp only [Nat.succ_sub_one] at bc
              rw [←hbn, pr_eq_prob, bool_prob_true_of_false, bob]; linarith
            · intro x _ xe
              simp only [xe, if_true, if_false, zero_add, one_mul, exp_const, le_refl]
            · intro _ _ _; apply exp_nonneg; intro _ _; apply add_nonneg ite_one_zero_nonneg
              apply mul_nonneg ite_one_zero_nonneg; linarith
          · apply le_exp_of_forall_le; intro r _; induction r
            · trans 1 - v; apply mul_le_of_le_one_right; linarith; linarith
              have vs := bob_sound o VeraId cs v0 (le_of_lt (not_le.mp ps))
              simp only [if_false, Option.some_inj, zero_mul, add_zero, @eq_comm _ false,
                exp_eq_prob, Nat.succ_sub_one, vera, bool_prob_false_of_true] at vs ⊢
              linarith
            · simp only [if_true, one_mul, if_false, zero_add, exp_const]
              apply mul_le_of_le_one_right; linarith; linarith
        · simp only [exp_add, exp_mul_const, Nat.succ_sub_one, ← hbn]
          convert le_refl _

/-- If Alice lies about probabilities by more than b, Bob usually catches Alice in a lie -/
lemma bobs_catches (o : Oracle) (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1)
    (qv : q ≤ v) {p : Vector ℝ n} {y : Vector Bool n} (pb : ¬close p (o.probs y) b) :
    (1 - v) * (1 - q) ^ n ≤ (bobs o (bob s b q) (vera c s v) p y).pr (λ r ↦ r = some false) := by
  induction' n with n h
  · simp only [Vector.eq_nil, close_nil, not_true_eq_false] at pb
  · by_cases pbn : close p.tail (o.probs y.tail) b
    · have safe := bobs_safe o cs sb q0 v0 v1 qv p.tail y.tail
      simp only [bobs, Nat.succ_sub_one, pr_bind, @exp_fintype (Option Bool), option_bool_univ,
        Finset.mem_singleton, Finset.mem_insert, not_false_eq_true, Finset.sum_insert, pr_pure,
        ite_false, mul_zero, ite_true, mul_one, Finset.sum_singleton, zero_add, ge_iff_le,
        vera_score] at safe ⊢
      generalize hbs : bobs o (bob s b q) (vera c s v) p.tail y.tail = bs
      simp only [hbs, Finset.mem_insert, some.injEq, Bool.true_eq_false, Finset.mem_singleton,
        or_self, not_false_eq_true, Finset.sum_insert, mul_zero, mul_one, Finset.sum_singleton,
        zero_add, Comp.prob', pr_pure, ↓reduceIte, pr_bind] at safe ⊢
      trans (bs.prob (some false) + bs.prob none * (1 - v)) * (1 - q)
      · refine le_trans ?_ (mul_le_mul_of_nonneg_right safe (by linarith))
        rw [mul_assoc, ←pow_succ]
      · simp only [add_mul]
        apply add_le_add
        · exact mul_le_of_le_one_right (prob_nonneg _) (by linarith)
        · rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (prob_nonneg _)
          simp only [Oracle.probs, Nat.succ_sub_one, close_succ, Vector.head_cons, Vector.tail_cons,
            pbn, and_true, not_le] at pb
          rw [mul_comm]
          refine le_exp_of_cut (fun x ↦ x = false) (1-q) (1-v) ?_ ?_ ?_ (by linarith)
          · have bs := bob_sound o BobId sb q0 (le_of_lt pb)
            simp only [Nat.succ_sub_one, bool_prob_false_of_true, pr_eq_prob, bob,
              Comp.prob'] at bs ⊢
            linarith
          · intro x _ x0
            have vs := bob_sound o VeraId cs v0 (le_of_lt (lt_trans sb pb))
            simp only [x0, if_false, Option.some_inj, exp_eq_prob, bool_prob_false_of_true, vera,
              Nat.succ_sub_one, Comp.prob'] at vs ⊢
            linarith
          · intro _ _ t
            simp only [Bool.not_eq_false] at t; simp only [t, if_true, if_false, exp_const, le_refl]
    · specialize h pbn
      refine le_trans ?_ (le_pr_bind_of_cut _ (1-q) h ?_ (by linarith))
      · rw [mul_assoc, pow_succ]
      · intro _ _ f; simp only [f, pr_pure, if_true]; linarith

/-- Bob wins the debate with probability ≥ 8/15 -/
theorem soundness' (o : Oracle) (L : o.lipschitz t k) (eve : Alice)
    (c0 : 0 < c) (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1) (qv : q ≤ v) :
    (1 - v) * (1 - q) ^ (t+1) * ((o.final t).prob false - k * b) ≤
      ((debate eve (bob s b q) (vera c s v) t).prob' o).prob false := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ge_iff_le,
    ← pr_eq_prob (alices _ _ _ >>= _)]
  have lies := evil_alices_lies o L eve (lt_trans c0 (lt_trans cs sb))
  rw [pr_neg', sub_le_iff_le_add, add_comm, ←sub_le_iff_le_add, bool_prob_true_of_false] at lies
  simp only [not_and_or, Bool.not_eq_true] at lies; ring_nf at lies
  rw [mul_comm]; refine le_pr_bind_of_cut _ ?_ lies ?_ ?_
  · intro (p,y) _ h; simp only [pr_map]; cases' h with h h
    · refine le_trans (bobs_catches o cs sb q0 v0 v1 qv h) ?_
      apply pr_mono; intro r _ e; simp only [e, extract]
    · simp only at h; simp only [pr]
      have safe := bobs_safe o cs sb q0 v0 v1 qv p y
      generalize hbs : bobs o (bob s b q) (vera c s v) p y = bs; simp only [hbs] at safe
      simp only [@exp_fintype (Option Bool), option_bool_univ, vera_score, Finset.mem_insert,
        some.injEq, Bool.true_eq_false, Finset.mem_singleton, or_self, not_false_eq_true,
        Finset.sum_insert, mul_zero, mul_one, Finset.sum_singleton, zero_add, extract, h, mul_ite,
        ↓reduceIte, ge_iff_le] at safe ⊢
      exact le_trans safe (add_le_add_left (mul_le_of_le_one_right (prob_nonneg _) (by linarith)) _)
  · apply mul_nonneg; linarith; apply pow_nonneg; linarith

/-
# Parameters

We now fill in parameters.  We are given

  w = win margin of the computation: 1/2 < w ≤ (o.final t).prob true if we're in the language
  k = Lipschitz constant of the oracle
  t = steps, eliding the +1 in t+1 above
  d = desired win margin of the debate protocol

and we must set

  c = completeness threshold, which honest Alice tries to stay within
  s = soundness threshold, outside of which Vera usually complains
  b = bad threshold, outside of which Bob usually complains
  q = Alice's and Bob's per-step failure probability (we assume these are equal for simplicity)
  v = Vera's failure probability

The sample counts are (ignoring ceils)

  an = samples (alice c q) = log (2/q) / (2 c^2)
  bn = samples (bob s b q) = samples (alice (b-s)/2 q) = 2 log (2/q) / (b-s)^2
  vn = samples (vera c s v) = 2 log (2/v) / (s-c)^2

From completeness and soundness, we have

  d = (1-v) (w - k c - (1 - (1-q)^t)) ~ (1-v) (w - k c - q t)
  d = (1-v) (1-q)^t (w - k b)         ~ (1-v) (1 - q t) (w - k b)

Let v vary subject to d > (1-v) w.  Then we need

  d/(1-v) = w - k c - q t
  d/(1-v) = (1 - q t) (w - k b)

We want Alice and Bob to need the same number of samples, so

  log (2/q) / (2 c^2) = 2 log (2/q) / (b-s)^2
  (b-s)^2 = 4 c^2
  b - s = 2c
  b = 2c + s

Meh, let's get very lazy:
-/

/-- A valid set of parameters for the debate protocol -/
structure Params (w d k : ℝ) (t : ℕ) where
  v : ℝ
  c : ℝ
  s : ℝ
  b : ℝ
  q : ℝ
  k0 : 0 < k
  c0 : 0 < c := by positivity
  cs : c < s
  sb : s < b
  q0 : 0 < q := by positivity
  q1 : q ≤ 1
  v0 : 0 < v := by positivity
  v1 : v ≤ 1
  qv : q ≤ v
  bw : k * b ≤ w
  complete : d ≤ (1-v) * (w - k * c - q * (t+1))
  sound : d ≤ (1-v) * (1 - q * (t+1)) * (w - k * b)

/-- Completeness for any valid parameters -/
theorem completeness_p (o : Oracle) (L : o.lipschitz t k) (eve : Bob)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob true) :
    d ≤ ((debate (alice p.c p.q) eve (vera p.c p.s p.v) t).prob' o).prob true := by
  refine le_trans (le_trans p.complete ?_) (completeness' o L eve p.c0 p.cs p.q0 p.q1 p.v0 p.v1)
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right m _) ?_) (by linarith [p.v1])
  rw [neg_le_neg_iff, sub_le_iff_le_add, add_comm, ←sub_le_iff_le_add, mul_comm, sub_eq_add_neg,
    ←mul_neg, ←Nat.cast_add_one]
  apply one_add_mul_le_pow; linarith [p.q1]

/-- Soundness for any valid parameters -/
theorem soundness_p (o : Oracle) (L : o.lipschitz t k) (eve : Alice)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob false) :
    d ≤ ((debate eve (bob p.s p.b p.q) (vera p.c p.s p.v) t).prob' o).prob false := by
  refine le_trans (le_trans p.sound ?_) (soundness' o L eve p.c0 p.cs p.sb p.q0 p.v0 p.v1 p.qv)
  simp only [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ ?_ ?_) (by linarith [p.v1])
  · rw [mul_comm, sub_eq_add_neg, ←mul_neg, ←Nat.cast_add_one]
    apply one_add_mul_le_pow
    linarith [p.q1]
  · apply add_le_add_right m
  · linarith [p.bw]
  · apply pow_nonneg; linarith [p.q1]
