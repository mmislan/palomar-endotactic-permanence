# Uniform permanence of endotactic reaction networks with measurable rates

Uniform permanence is established for finite endotactic reaction networks with arbitrary real complexes and measurable rate coefficients bounded above and away from zero almost everywhere. Each positive stoichiometric compatibility class contains a compact convex forward-invariant absorbing set, with entry times uniform over compact sets of initial conditions and all rate histories within a fixed rate box. Global positive Carathéodory solutions exist and are unique, and an exponential continuous-dependence estimate holds for initial data under a common rate history on a compact positive region. The result resolves the Endotactic Permanence Conjecture stated as Conjecture 1.3 by Johnston, Pantea and Donnell (https://arxiv.org/abs/1412.4662), using an ordinary-endotactic drift estimate together with the finite affine barrier construction from OpenAI’s work on weakly reversible networks.

The [paper](paper/main.pdf) gives the mathematical argument. The [claim map](CLAIM_MAP.md) relates the formal statements to the conjecture and the manuscript.

## Formal statements

[Challenge.lean](Challenge.lean) states uniform permanence and continuous dependence with explicit definitions. [Solution.lean](Solution.lean) proves both statements using the development in [proofs/EndotacticPermanence](proofs/EndotacticPermanence). The absorbing set is chosen before the initial compact set and rate history; the entry time is chosen before the initial point and history. Uniqueness is among positive Carathéodory solutions.

The project pins Lean 4.35.0-rc2 and its Mathlib dependencies. The two selected declarations passed local Comparator and six kernel checks; [verification/local-check.json](verification/local-check.json) identifies the exact checked sources and records the results. The [build guide](BUILD.md) describes reproduction.

## Attribution

The affine barrier construction adapts the [OpenAI mass-action development](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/MassAction). Source attribution is recorded in [NOTICE](NOTICE) and [UPSTREAM_PROVENANCE.json](UPSTREAM_PROVENANCE.json). The new argument supplies ordinary-endotactic drift estimates and the measurable-rate permanence theorem. Formalization authorship and AI assistance are recorded in [formalization.yaml](formalization.yaml).
