import Debate.Cost
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

/-- The debate protocol is correct with probability 3/5, using the default parameters -/
theorem correctness (k : ℝ) (k0 : 0 < k) (t : ℕ) :
    let p := defaults k t k0
    Correct (3/5) k t (alice p.c p.q) (bob p.s p.b p.q) (vera p.c p.s p.v) where
  half_lt_w := by norm_num
  complete o eve L m := completeness o L eve (defaults k t k0) m
  sound o eve L m := soundness o L eve (defaults k t k0) m
