import Mathlib.Topology.MetricSpace.Basic
import Prob.Defs

/-!
Stochastic oracle as a model of general, randomized computations

We formalize debate w.r.t. randomized computations allowed to query a stochastic oracle.
For simplicity, we embed all details of the computation as the oracle, including deterministic
features.  Concretely, we start with zero bits, and repeatedly prepend bits from the oracle
for some number of steps.  The final bit is the result.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
noncomputable section

/-- A stochastic oracle -/
def Oracle := (n : ℕ) → Vector Bool n → Prob Bool

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as o can behave differently based on input length. -/
def Oracle.fold (o : Oracle) : (n : ℕ) → Prob (Vector Bool n)
| 0 => pure Vector.nil
| n+1 => do
  let y ← o.fold n
  let x ← o _ y
  return y.cons x

/-- The (n+1)th bit of o.fold -/
def Oracle.final (o : Oracle) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- The distance between two oracles is the sup of their probability differences -/
instance : Dist Oracle where
  dist o0 o1 := ⨆ n, ⨆ y : Vector Bool n, |(o0 _ y).prob true - (o1 _ y).prob true|

/-- An oracle computation is k-Lipschitz if the final probability differs by ≤ k * oracle dist.
    We define this asymmetrically, as we want the neighborhood of a particular oracle. -/
structure Oracle.lipschitz (o : Oracle) (t : ℕ) (k : ℝ) : Prop where
  k0 : 0 ≤ k
  le : ∀ o' : Oracle, |(o.final t).prob true - (o'.final t).prob true| ≤ k * dist o o'
