module
public import proofs.EndotacticPermanence.Real.ClampedMassAction
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open Set MeasureTheory

theorem interval_integral_mem_submodule {d : ℕ} (S : Submodule ℝ (Fin d → ℝ))
    {g : ℝ → (Fin d → ℝ)} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (hmem : ∀ t, g t ∈ S) :
    (∫ t in a..b, g t) ∈ S := by
  let : IsClosed (S : Set (Fin d → ℝ)) := S.closed_of_finiteDimensional
  have hz : S.mkQL (∫ t in a..b, g t) = 0 := by
    rw [← S.mkQL.intervalIntegral_comp_comm hg]
    have heq : (fun t => S.mkQL (g t)) = fun _ => 0 := by
      funext t
      exact (Submodule.Quotient.mk_eq_zero S).mpr (hmem t)
    rw [heq]
    simp
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

variable {d : ℕ} {R : Type*} [Fintype R]

theorem clamped_integral_curve_in_class (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ) (a b : Fin d → ℝ) (hab : a ≤ b)
    {c x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx0 : x0 - c ∈ stoichiometricSubspace source target)
    (hx : ∀ T : ℝ, 0 ≤ T →
      IsIntegralCurveOn (clampedMassAction source target B k a b hab) x0 T x) :
    ∀ t : ℝ, 0 ≤ t → x t - c ∈ stoichiometricSubspace source target := by
  intro t ht
  have h := hx t ht
  rw [h.2 t ⟨ht, le_rfl⟩]
  have hi := interval_integral_mem_submodule (stoichiometricSubspace source target) h.1
    (fun u => indexed_mass_action_mem_span source target
      (OAI.Problem326.coordinateClamp B.lower B.upper B.lower_le_upper (k u))
      (OAI.Problem326.coordinateClamp a b hab (x u)))
  have heq : x0 + (∫ u in (0 : ℝ)..t,
      clampedMassAction source target B k a b hab u (x u)) - c =
      (x0 - c) + ∫ u in (0 : ℝ)..t,
        clampedMassAction source target B k a b hab u (x u) := by abel
  rw [heq]
  exact Submodule.add_mem _ hx0 hi

end
end EndotacticPermanence.RealComplex
