import Comp.Oracle
import Prob.Defs

/-!
## Oracle-relative probabilitistic computations

`Prob α` represents the result of a probabilistic computation, but has no information about
how long the computation took.  `Comp s α` is a computation that is allowed to consult any
oracle `o ∈ s`, and produces a distribution over results and calls to each oracle.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {I : Type}
variable {s t : Set I}
variable {α β γ : Type}

/-- A stochastic computation that can make oracle queries.
    Importantly, the computation does not know the oracle, so we can model query complexity.
    The `Comp` constructors are not very user friendly due to kernel restrictions on inductive,
    but we replace them with clean ones below. -/
inductive Comp {I : Type} (s : Set I) (α : Type) : Type 1 where
  /-- Return a result with no computation -/
  | pure' : α → Comp s α
  /-- Sample a value with some probability distribution, then continue -/
  | sample' : {β : Type} → Prob β → (β → Comp s α) → Comp s α
  /-- Query an oracle `o ∈ s`, and branch on the result -/
  | query' : (o : I) → o ∈ s → (n : ℕ) → Vector Bool n → Comp s α → Comp s α → Comp s α

namespace Comp

/-- Bind two `Comp`s together -/
def bind' (f : Comp s α) (g : α → Comp s β) : Comp s β := match f with
  | .pure' x => g x
  | .sample' p f => .sample' p (fun y ↦ (f y).bind' g)
  | .query' o m n y f0 f1 => .query' o m n y (f0.bind' g) (f1.bind' g)

/-- `Comp` is a monad -/
instance : Monad (Comp s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- `Prob`s are `Comp s` for any `s` -/
instance : Coe (Prob α) (Comp s α) where
  coe f := .sample' f pure

/-- The simplest case of `Comp.query'` -/
def query (i : I) {n : ℕ} (y : Vector Bool n) : Comp {i} Bool :=
  Comp.query' i (mem_singleton _) n y (pure true) (pure false)

/-- The value and query counts of a `Comp s`, once we supply oracles -/
def run (f : Comp s α) (o : I → Oracle) : Prob (α × (I → ℕ)) := match f with
  | .pure' x => pure (x, fun _ => 0)
  | .sample' f g => f >>= fun x ↦ (g x).run o
  | .query' i _ n y f0 f1 => do
    let x ← (o i) n y
    let (z,c) ← if x then f0.run o else f1.run o
    return (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp s` -/
def prob (f : Comp s α) (o : I → Oracle) : Prob α :=
  Prod.fst <$> f.run o

/-- The value of a `Comp s` when all oracles are the same -/
@[simp] def prob' (f : Comp s α) (o : Oracle) : Prob α :=
  f.prob fun _ ↦ o

/-- The expected query cost of a `Comp α`.
    There is a design decision here to make the theory about expected cost.  My guess is that
    will make the downstream theory slightly easier. -/
def cost (f : Comp s α) (o : I → Oracle) (i : I) : ℝ :=
  (f.run o).exp fun (_,c) ↦ c i

/-- The expected query cost of a `Comp α` when all oracles are the same. -/
def cost' (f : Comp s α) (o : Oracle) : I → ℝ :=
  f.cost fun _ ↦ o

/-- Allow more oracles in a computation -/
def allow (f : Comp s α) (st : s ⊆ t) : Comp t α := match f with
  | .pure' x => pure x
  | .sample' f g => f >>= fun x ↦ (g x).allow st
  | .query' i m n y f0 f1 => .query' i (st m) n y (f0.allow st) (f1.allow st)

/-- Allow all oracles in a computation -/
def allow_all (f : Comp s α) : Comp (@univ I) α :=
  f.allow (subset_univ s)

end Comp
