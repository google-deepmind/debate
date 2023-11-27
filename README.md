Stochastic doubly-efficient debate formalization
================================================

**Summary:** We formalize the correctness of the main stochastic oracle
doubly-efficient debate protocol from
[Brown-Cohen, Irving, Piliouras (2023), Scalable AI safety via doubly-efficient debate.](https://arxiv.org/abs/2311.14125)
in Lean 4.

[Irving, Christiano, Amodei (2018), AI safety via debate](https://arxiv.org/abs/1805.00899)
is one approach to AI alignment of strong agents, using two agents ("provers")
competing in a zero-sum game to convince a human judge ("verifier") of the truth
or falsify of a claim.  Theoretically, if we model the judge as a polynomial
time Turing machine, optimal play in the debate game can convince the judge of
any statement in PSPACE.  However, this theoretical model is limited in several
ways: the agents are assumed to have unbounded computational power, which is not
a realistic assumption for ML agents, and the results consider only
deterministic arguments.

[Brown-Cohen, Irving, Piliouras (2023), Scalable AI safety via doubly-efficient debate.](https://arxiv.org/abs/2311.14125)
improves the complexity theoretic model of debate to be "doubly-efficient": both
the provers and the verifier have limited computational power.  It also treats
stochastic arguments: the provers try to convince the judge of the result of a
randomized computation involving calls to a random oracle.  Concretely, the main
formalized result is

**Definition 6.1 (Lipschitz oracle machines).** An oracle Turing machine
$M^\mathcal{O}$ is $K$-Lipschitz if, for any other oracle $\mathcal{O}'$ s.t.
$|\Pr(\mathcal{O}(z)) - \Pr(\mathcal{O}'(z))| \le \epsilon$, we have
$|\Pr(M^\mathcal{O}(x)) - \Pr(M^\mathcal{O'}(x))| \le K \epsilon$.

**Theorem 6.2 (doubly-efficient stochastic oracle debate).** Let $L$ be a
language decidable by a $K$-Lipschitz probabilistic oracle Turing machine
$M^\mathcal{O}$ in time $T = T(n)$, measuring oracle queries only as costing
time.  Then there is an $O(K^2 T \log T)$ prover time, $O(K^2)$ verifier time
debate protocol with cross-examination deciding $L$ with completeness $3/5$ and
soundness $3/5$.

The formalized result differs from the paper result slightly in that we focus
only on correctness: we do not yet formalize space complexity, count only oracle
queries for time complexity, and represent those queries only via the code for
the protocol.  We also define Lipschitz oracle machines differently: the paper
fixes $M$ and lets both $\mathcal{O}$ and $\mathcal{O}'$ vary, while we fix both
$M$ and $\mathcal{O}$ and let only $\mathcal{O}'$ vary (this slightly
strengthens the resulting theorem).

1. `Prob/Defs.lean`: Finitely supported probability distributions, representing stochastic computations.
2. `Comp/Defs.lean`: Stochastic computations relative to a set of oracles.
3. `Comp/Oracle.lean`: Our computation model, including the definition of Lipschitz oracles.
4. `Debate/Protocol.lean`: The debate protocol, honest players, and the definition of correctness.
5. `Debate/Correct.lean`: The final correctness theorems.
6. `Debate/Details.lean`: Proof details.
7. `Debate/Cost.lean`: Query complexity of each player.

## Acknowledgements

We thank [Eric Wieser](https://github.com/eric-wieser) for his careful review
and many helpful suggestions.  The code is much better as a result!

## Installation

1. Install Lean 4 and Lake via elan: https://github.com/leanprover/elan
2. Run `lake build` within the directory.

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
