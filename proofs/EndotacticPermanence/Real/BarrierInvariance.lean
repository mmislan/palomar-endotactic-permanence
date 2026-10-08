module
public import proofs.EndotacticPermanence.Real.GlobalMassAction
public import proofs.EndotacticPermanence.Real.BarrierFamily

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

theorem BarrierAt.invariant {source target : R → Fin d → ℝ} {B : PositiveRateBox R}
    {G : GeometricFamily d (sourceComparisons source)} {c : Fin d → ℝ} {h : ℝ}
    (C : BarrierAt source target B G c h) (hh : 0 < h) (hh1 : h < 1)
    (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e))
    (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    {x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx0K : x0 ∈ C.plateau) (hx0S : x0 - c ∈ stoichiometricSubspace source target)
    (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x)
    (hxpos : ∀ t : ℝ, 0 ≤ t → OAI.Problem326.PositiveState (x t)) :
    ∀ t : ℝ, 0 ≤ t → x t ∈ C.plateau := by
  obtain ⟨y, hy, hyt, hyclass⟩ := exists_trapped_mass_action_curve source target B G c hh hh1
    C.margin_pos C.zero_slope C.active (C.box_interior hh hh1) C.drift k hk hkbox x0 hx0K hx0S
  have heq := forward_mass_action_unique source target B k hk hkbox hx hy hxpos (fun t ht => (hyclass t ht).1)
  intro t ht
  rw [heq ht]
  exact hyt t ht

end
end EndotacticPermanence.RealComplex
