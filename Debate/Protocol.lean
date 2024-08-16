import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Comp.Oracle
import Comp.Defs
import Prob.Bernoulli
import Prob.Estimate

/-!
The stochastic oracle doubly-efficient debate protocol
-/

open Classical
open Comp
open Prob
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {n : ℕ}

/-- We distinguish debater and verify oracles so that we can measure cost separately
    for different agents.  We will plug in the same oracles in the end for all ids. -/
inductive OracleId where
  | AliceId : OracleId
  | BobId : OracleId
  | VeraId : OracleId

export OracleId (AliceId BobId VeraId)
abbrev AllIds := @univ OracleId

-- Next, we give type signatures for Alice and Bob, and the protocol that connects them.
-- See Figure 1 in the paper for the corresponding prose description.  We differ from Figure 1
-- in that we treat steps (2b,2c,2d) as fixed parts of the protocol, rather than agent moves.

/-- The state of a debate.  Either
    1. An uninterrupted Vector Bool n trace, or
    2. A final result if we rejected. -/
def State (n : ℕ) := Except Bool (Vector Bool n)

/-- Alice takes the transcript so far and estimates a probability that the next step is 1.
    Alice's goal is to produce output 1.  An honest Alice will try to mimic Oracle.fold. -/
def Alice' (o : OracleId) := (n : ℕ) → Vector Bool n → Comp {o} ℝ

/-- Alice using the normal `AliceId` -/
def Alice := Alice' AliceId

/-- Bob sees the transcript and Alice's claimed probability, and decides whether to continue.
    Technically in Figure 4 Bob also sees the chosen bit, but this is irrelevant to the protocol.
    In the game, Bob's goal is to produce output 0.  An honest Bob will yell iff Alice doesn't
    mimic Oracle.fold. -/
def Bob' (o : OracleId) := (n : ℕ) → Vector Bool n → ℝ → Comp {o} Bool

/-- Bob using the normal `BobId` -/
def Bob := Bob' BobId

/-- Verifiers have an identical type signature to Bob, but use weaker parameters. -/
def Vera := (n : ℕ) → Vector Bool n → ℝ → Comp {VeraId} Bool

/-- Enough samples to estimate a probability with error < e with failure probability ≤ q -/
def samples (e q : ℝ) : ℕ := Nat.ceil (-Real.log (q/2) / (2 * e^2))

/-- Honest Alice estimates the correct probability within error < e with failure probability ≤ q -/
def alice' (e q : ℝ) (o : OracleId) : Alice' o := λ _ y ↦
  estimate (query o y) (samples e q)

def alice (e q : ℝ) : Alice := alice' e q AliceId

/-- Honest Bob checks the probability against an honest copy of Alice.

    Bob has separate soundness and completeness conditions, but (for now) uses a single estimation
    with a single failure probability.  We need
    1. Completeness: If Alice is off by ≤ c, Bob should accept with probability ≥ 1-q
    2. Soundness: If Alice is off by ≥ s, Bob should reject with probability ≥ 1-q
    Assume Bob estimates p to within e, then rejects iff his estimate differs from Alice by > r.
    1. Completeness: To accept if Alice is off by ≤ c, we need c ≤ r - e
    2. Soundness: To reject if Alice is off by ≥ s, we need r + e ≤ s
    We want e as large as possible to reduce the number of samples.  This is achieved if
      r = (c + s) / 2
      e = (s - c) / 2 -/
def bob' (c s q : ℝ) (o : OracleId) : Bob' o := λ _ y p ↦
  return |p - (←alice' ((s-c)/2) q o _ y)| < (c+s)/2

def bob (c s q : ℝ) : Bob := bob' c s q BobId

/-- The verifier checks the probability estimate given by Alice.
    We reuse Honest Bob with a weaker error probability, which we will set later. -/
def vera (s v q : ℝ) : Vera := bob' s v q VeraId

/-- One step of the debate protocol -/
def step (alice : Alice) (bob : Bob) (vera : Vera) (y : Vector Bool n) :
    Comp AllIds (State (n+1)) := do
  let p ← (alice _ y).allow_all
  if ←(bob _ y p).allow_all then do  -- Bob accepts Alice's probability, so take the step
    let x ← bernoulli p  -- This is Figure 4, steps 2b,2c,2d, as a fixed part of the protocol
    return .ok (y.cons x)
  else  -- Bob rejects, so we call the verifier and end the computation
    return .error (←(vera _ y p).allow_all)

/-- n steps of the debate protocol -/
def steps (alice : Alice) (bob : Bob) (vera : Vera) : (n : ℕ) → Comp AllIds (State n)
| 0 => pure (.ok Vector.nil)
| n+1 => do match ←steps alice bob vera n with
  | .ok y => step alice bob vera y
  | .error r => return .error r

/-- The full debate protocol that stitches these together -/
def debate (alice : Alice) (bob : Bob) (vera : Vera) (t : ℕ) : Comp AllIds Bool := do
  match ←steps alice bob vera (t+1) with
  | .ok y => return y.head
  | .error r => return r

-- Next, we define what it means for the debate protocol to be correct.  The definition is
-- in this file to keep the details of the proof separated.  See Correct.lean for the final
-- Correct result, and Details.lean for the proof.

/-- The debate protocol is correct if, for all k-Lipschitz oracles o
    1. Whenever Pr(o.final) ≥ 2/3, Honest Alice beats any Bob (Eve) with probability w > 1/2
    2. Whenever Pr(o.final) ≤ 1/3, Honest Bob beats any Alice (Eve) with probability w > 1/2 -/
structure Correct (w k : ℝ) (t : ℕ) (alice : Alice) (bob : Bob) (vera : Vera) : Prop where
  /-- Success is more likely than failure -/
  half_lt_w : 1/2 < w
  /-- If we're in the language, Alice wins -/
  complete : ∀ (o : Oracle) (eve : Bob), o.lipschitz t k → (o.final t).prob true ≥ 2/3 →
    ((debate alice eve vera t).prob' o).prob true ≥ w
  /-- If we're out of the language, Bob wins -/
  sound : ∀ (o : Oracle) (eve : Alice), o.lipschitz t k → (o.final t).prob false ≥ 2/3 →
    ((debate eve bob vera t).prob' o).prob false ≥ w
