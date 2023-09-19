Stochastic doubly efficient debate formalization
================================================

**Summary:** We formalize the correctness of the main stochastic oracle
doubly-efficient debate protocol from Anonymous et al. in Lean 4.

https://arxiv.org/abs/1805.00899 is one approach to AI alignment of strong
agents, using two agents ("provers") competing in a zero-sum game to convince a
human judge ("verifier") of the truth or falsify of a claim.  Theoretically, if
we model the judge as a polynomial time Turing machine, optimal play in the
debate game can convince the judge of any statement in PSPACE.  However, this
theoretical model is limited in several ways: the agents are assumed to have
unbounded computational power, which is not a realistic assumption for ML
agents, and the results consider only deterministic arguments.

Anonymous et al. (TODO: link) improves the complexity theoretical model of
debate to be "doubly-efficient": both the provers and the verifier have limited
computational power.  It also treats stochastic arguments: the provers try to
convince the judge of the result of a randomized computation involving calls to
a random oracle.  Concretely, the main theorem is

**Theorem 7.2 (doubly-efficient stochastic oracle debate).** For an integer $d >
0$, let $\mathcal{O}$ be a $d$-discrete stochastic oracle (an random function
mapping length $l$ bit strings to bits, where probabilities are integer
multiples of $1/d$. Let $L$ be any language decidable by a probabilistic oracle
Turing machine $M^\mathcal{O}$ in time $T = T(n)$ and space $S = S(n)$.  Then
there is a $O(d^2 T \log T)$ prover time, $O(d^2 + l)$ verifier time debate
protocol with cross-examination deciding $L$ with completeness $3/5$ and
soundness $3/5$.

This repo formalizees this result in Lean 4 (mostly: we do not formalize the
space constraint, formalize the time constraint only implicitly by defining
time-limited honest provers and verifiers, and a have weaker completeness and
soundness constant $8/15$.  The key files are:

1. `Prob/Defs.lean`: Finitely supported probability distributions, representing stochastic computations.
2. `Debate/Protocol.lean`: The debate protocol, honest players, and the definition of correctness.
3. `Debate/Correct.lean`: The final correctness theorems.
4. `Debate/Details.lean`: Proof details.

## Installation (TODO)

Write instructions for how the user should install your code. The instructions
should ideally be valid when copy-pasted. You can combine this with the Usage
section if there's no separate installation step.

## Citing this work (TODO)

Add citation details here, usually a pastable BibTeX snippet.

## License and disclaimer

Copyright 2023 DeepMind Technologies Limited

All software is licensed under the Apache License, Version 2.0 (Apache 2.0);
you may not use this file except in compliance with the Apache 2.0 license.
You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY licenses are
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.
