import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Prob.Bernoulli
import Prob.Estimate

/-!
The stochastic oracle doubly-efficient debate protocol
-/

open Classical
open Prob
open Option (some none)
open scoped Real
noncomputable section

variable {n : ℕ}

-- We define a very simple randomized computation conditioning on a random oracle.
-- We repeatedly prepend bits from the oracle for n+1 steps, giving the oracle all previous
-- bits as input, and the final bit is the result.

/-- A stochastic oracle -/
def Oracle := List Bool → Prob Bool

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as o can behave differently based on input length. -/
def Oracle.fold (o : Oracle) : (n : ℕ) → Prob (Vector Bool n)
| 0 => pure Vector.nil
| n+1 => do
  let y ← o.fold n
  let x ← o y.toList
  return y.cons x

/-- The (n+1)th bit of o.fold -/
def Oracle.final (o : Oracle) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- An oracle is d-discrete if its probabilities are multiples of 1/d -/
class Discrete (o : Oracle) (d : ℕ) : Prop where
  /-- The granuality of probabilities -/
  d0 : 0 < (d : ℝ)
  /-- Probabilities are multiples of 1/d -/
  disc : ∀ x y, ∃ a : ℕ, (o x).prob y = a/d

-- Next, we give type signatures for Alice and Bob, and the protocol that connects them.
-- See Figure 4 in the paper for the corresponding prose description.  We differ from Figure 4
-- in that we treat steps (2b,2c,2d) as fixed parts of the protocol, rather than moves by the agents.

/-- The state of a debate.  Either
    1. An uninterrupted Vector Bool n trace, or
    2. A final result if we rejected. -/
def State (n : ℕ) := Except Bool (Vector Bool n)

/-- Alice takes the transcript so far and estimates a probability that the next step is 1.
    In the game, Alice's goal is to produce output 1.  An honest Alice will try to mimic Oracle.fold. -/
def Alice := (n : ℕ) → Vector Bool n → Prob ℝ

/-- Bob sees the transcript and Alice's claimed probability, and decides whether to continue.
    Technically in Figure 4 Bob also sees the chosen bit, but this is irrelevant to the protocol.
    In the game, Bob's goal is to produce output 0.  An honest Bob will yell iff Alice doesn't
    mimic Oracle.fold. -/
def Bob := (n : ℕ) → Vector Bool n → ℝ → Prob Bool

/-- Enough samples to estimate p with error < 1/2d with probability ≥ 1-e
    The required number of samples depends on the total number of steps t. -/
def samples (d : ℕ) (e : ℝ) : ℕ := Nat.ceil ((-2:ℝ) * (d:ℝ)^2 * Real.log (e/2))

/-- Honest Alice estimates the correct p via sampling with error probability e -/
def alice' (o : Oracle) (d : ℕ) (e : ℝ) : Alice := λ _ y ↦ do
  let q ← estimate (o y.toList) (samples d e)
  return round (q * d) / d

/-- Honest Alice with error probability suitable for t+1 steps -/
def alice (o : Oracle) (d : ℕ) (t : ℕ) : Alice := alice' o d (1/(10*(↑t+1)))

/-- Honest Bob checks the probability against an honest copy of Alice -/
def bob' (o : Oracle) (d : ℕ) (e : ℝ) : Bob := λ _ y p ↦ return p = (←alice' o d e _ y)

/-- Honest Bob with error probability suitable for t+1 steps -/
def bob (o : Oracle) (d : ℕ) (t : ℕ) : Bob := bob' o d (1/(10*(↑t+1)))

/-- The verifier checks the probability estimate given by Alice.
    We reuse Honest Bob with a weaker error probability. -/
def vera (o : Oracle) (d : ℕ) (y : Vector Bool n) (p : ℝ) : Prob Bool := bob' o d (1/9) _ y p

/-- One step of the debate protocol -/
def step (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) (y : Vector Bool n) : Prob (State (n+1)) := do
  let p ← alice _ y
  if ←bob _ y p then do  -- Bob accepts Alice's probability, so take the step
    let x ← bernoulli p  -- This is Figure 4, steps 2b,2c,2d, as a fixed part of the protocol
    return Except.ok (y.cons x)
  else  -- Bob rejects, so we call the verifier and end the computation
    return Except.error (←vera o d y p)

/-- n steps of the debate protocol -/
def steps (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) : (n : ℕ) → Prob (State n)
| 0 => pure (Except.ok Vector.nil)
| n+1 => do match ←steps o d alice bob n with
  | Except.ok y => step o d alice bob y
  | Except.error r => return Except.error r

/-- The full debate protocol that stitches these together -/
def debate (o : Oracle) (d : ℕ) (alice : Alice) (bob : Bob) (t : ℕ) : Prob Bool := do
  match ←steps o d alice bob (t+1) with
  | Except.ok y => return y.head
  | Except.error r => return r

-- Next, we define what it means for the debate protocol to be correct.  The definition is
-- in this file to keep the details of the proof separated.  See Correct.lean for the final
-- Correct result, and Details.lean for the proof.

/-- The debate protocol is correct if, for all oracles o
    1. Whenever Pr(o.final) ≥ 2/3, Honest Alice beats arbitrary Bob (Eve) with probability w > 1/2
    2. Whenever Pr(o.final) ≤ 1/3, Honest Bob beats aribtrary Alice (Eve) with probability w > 1/2 -/
structure Correct (w : ℝ) : Prop where
  /-- Success is more likely than failure -/
  half_lt_w : 1/2 < w
  /-- If we're in the language, Alice wins -/
  complete : ∀ (o : Oracle) (d t : ℕ) [Discrete o d] (eve : Bob), (o.final t).prob true ≥ 2/3 →
    (debate o d (alice o d t) eve t).prob true ≥ w
  /-- If we're out of the language, Bob wins -/
  sound : ∀ (o : Oracle) (d t : ℕ) [Discrete o d] (eve : Alice), (o.final t).prob true ≤ 1/3 →
    (debate o d eve (bob o d t) t).prob false ≥ w
