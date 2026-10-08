module
public import proofs.EndotacticPermanence.MassActionModel
public import proofs.EndotacticPermanence.CaratheodoryCurve
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set MeasureTheory Metric
open scoped BigOperators NNReal Topology

variable {d : ℕ} {R : Type*} [Fintype R]

theorem contDiff_indexed_mass_action (source target : R → Fin d → ℕ) :
    ContDiff ℝ 1 (fun kx : (R → ℝ) × (Fin d → ℝ) =>
      indexedMassAction source target kx.1 kx.2) := by
  unfold indexedMassAction monomial
  fun_prop

/-- The rate box supplies uniform local bounds, rather than assuming trajectory bounds. -/
theorem uniform_mass_action_bounds (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (x0 : Fin d → ℝ) (a : NNReal) :
    ∃ L K : NNReal,
      (∀ k : R → ℝ, B.Contains k → ∀ x ∈ closedBall x0 a,
        ‖indexedMassAction source target k x‖ ≤ L) ∧
      (∀ k : R → ℝ, B.Contains k →
        LipschitzOnWith K (indexedMassAction source target k) (closedBall x0 a)) := by
  let C : Set ((R → ℝ) × (Fin d → ℝ)) :=
    Icc B.lower B.upper ×ˢ closedBall x0 a
  have hcompact : IsCompact C := isCompact_Icc.prod (isCompact_closedBall x0 a)
  have hconvex : Convex ℝ C := (convex_Icc B.lower B.upper).prod (convex_closedBall x0 a)
  have hdiff := contDiff_indexed_mass_action source target
  obtain ⟨K, hK⟩ := hdiff.contDiffOn.exists_lipschitzOnWith (by norm_num) hconvex hcompact
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hdiff.continuous.continuousOn
  let L : NNReal := ⟨max M 0, le_max_right _ _⟩
  refine ⟨L, K, ?_, ?_⟩
  · intro k hk x hx
    have hkmem : k ∈ Icc B.lower B.upper :=
      ⟨fun e => (hk e).1, fun e => (hk e).2⟩
    exact (hM (k, x) ⟨hkmem, hx⟩).trans (le_max_left M 0)
  · intro k hk x hx y hy
    have hkmem : k ∈ Icc B.lower B.upper :=
      ⟨fun e => (hk e).1, fun e => (hk e).2⟩
    have h := hK (show (k, x) ∈ C from ⟨hkmem, hx⟩)
      (show (k, y) ∈ C from ⟨hkmem, hy⟩)
    simpa only [Prod.edist_eq, edist_self, max_eq_right zero_le] using h

end EndotacticPermanence
