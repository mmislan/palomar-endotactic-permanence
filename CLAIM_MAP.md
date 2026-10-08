# Independent claim correspondence

The named Permanence Conjecture is Conjecture 1.3 of Johnston, Pantea and
Donnell, *A computational approach to persistence, permanence, and endotacticity
of biochemical reaction systems*, [arXiv:1412.4662](https://arxiv.org/abs/1412.4662). The independent Challenge
uses the adverse-reaction/earlier-positive-witness condition of Definition 3.1(1).
Compact containment in a positive stoichiometric class implies the eventual
coordinate bounds required by Definition 2.3. Complexes here have arbitrary
signed real coordinates, encompassing the nonnegative and integer cases.

| Item | Exact compared formulation |
|---|---|
| Network | Finite indexed reactions and finitely many species; real source and target vectors |
| Endotacticity | Every real direction; every strictly adverse reaction has a strictly earlier source and strictly positive displacement projection |
| Kinetics | Generalized mass action, exp(sum of source coordinate times log concentration), evaluated on positive states |
| Rates | Coordinatewise a.e. measurable on forward time; simultaneous a.e. bounds in a fixed positive rate box |
| Class | Positive part of the affine translate of the real reaction-displacement span |
| Absorbing set | One nonempty compact convex K in the class, selected before the initial compact set and rate history |
| Deadline | For every compact Q in the class, one T(Q) >= 0 selected before x0 and the rate history |
| Existence | A global forward locally absolutely continuous curve satisfying the ODE a.e.; positive and in the class at every forward time |
| Absorption | Every forward time u >= T(Q) lies in K |
| Uniqueness | All positive Caratheodory competitors agree at every forward time |
| Invariance | Every positive solution from K stays in K under every admissible history |
| Stability | On a fixed compact positive C, one Lipschitz constant before the common history and curves; exponential initial-data distance bound |

The solution does not assume a supplied trapping certificate, conservation law,
full rank, boundedness of an existing trajectory, weak reversibility or strong
endotacticity. Challenge imports no local proof modules. Its definitions are
explicit; the two statement holes are deliberately confined to Challenge.
Solution imports neither Challenge nor its axioms.

The main permanence theorem and initial-data stability estimate are selected
for comparison. Periodic forcing, autonomous equilibria, feedback and the
fixture-specific parts of the three-species example are conventional manuscript
arguments. Historical scalar comparison checks do not certify that full example.

The saved local verification of the selected declarations is summarized in `verification/local-check.json`, including exact source hashes and kernel results.
