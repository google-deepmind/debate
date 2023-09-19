import Debate.Details
import Debate.Protocol

/-!
Correctness of the stochastic oracle doubly-efficient debate algorithm
-/

open Classical
open Prob
open scoped Real
noncomputable section

/-- If Pr(o.final) ≥ 2/3, Alice wins the debate with probability ≥ 8/15 -/
theorem completeness (o : Oracle) (d t : ℕ) [Discrete o d] (m : (o.final t).prob true ≥ 2/3) (eve : Bob) :
    (debate o d (alice o d t) eve t).prob true ≥ 8/15 := completeness' o d t m eve

/-- If Pr(o.final) ≤ 1/3, Bob wins the debate with probability ≥ 8/15 -/
theorem soundness (o : Oracle) (d t : ℕ) [Discrete o d] (m : (o.final t).prob true ≤ 1/3) (eve : Alice) :
    (debate o d eve (bob o d t) t).prob false ≥ 8/15 := soundness' o d t m eve

/-- Summary: The debate protocol is correct, with win probability ≥ 8/15 > 1/2 -/
theorem correctness : Correct (8/15) where
  half_lt_w := by norm_num
  complete o d t _ eve m := completeness o d t m eve
  sound o d t _ eve m := soundness o d t m eve
