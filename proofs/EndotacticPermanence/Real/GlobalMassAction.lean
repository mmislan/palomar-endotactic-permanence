module
public import proofs.EndotacticPermanence.Real.ForwardUniqueness
public import proofs.EndotacticPermanence.Real.PlateauBox
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

/-- Ordinary endotacticity yields unique global positive solutions for every
admissible measurable history, without a prior trajectory bound. -/
theorem global_mass_action_existence (source target : R → Fin d → ℝ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e))
    (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ x : ℝ → (Fin d → ℝ),
      IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x ∧
      (∀ t : ℝ, 0 ≤ t → PositiveState (x t)) ∧
      (∀ y : ℝ → (Fin d → ℝ),
        IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 y →
          (∀ t : ℝ, 0 ≤ t → PositiveState (y t)) → EqOn x y (Ici 0)) := by
  obtain ⟨G⟩ := exists_geometric_family d (sourceComparisons source)
  obtain ⟨η, hη, _, hη1, hbar⟩ := exists_endotactic_barriers source target endo B G x0 hx0
  have hh : 0 < η / 2 := by positivity
  have hhη : η / 2 < η := by linarith
  have hh1 : η / 2 < 1 := hhη.trans_le hη1
  obtain ⟨j0, K, δ, hz, _, _, hx0K, hKinner, hK, hδ, hmargin⟩ := hbar (η / 2) hh hhη
  obtain ⟨x, hx, _, hclass⟩ := exists_trapped_mass_action_curve source target B G x0
    hh hh1 hδ hz hK (hKinner.trans (sqrt_box_subset_box hh hh1)) hmargin k hk hkbox
    x0 hx0K (by simp)
  exact ⟨x, hx, fun t ht => (hclass t ht).1,
    fun y hy hypos => forward_mass_action_unique source target B k hk hkbox hx hy
      (fun t ht => (hclass t ht).1) hypos⟩

end
end EndotacticPermanence.RealComplex
