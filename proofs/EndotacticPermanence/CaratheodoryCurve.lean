module
public import proofs.EndotacticPermanence.MeasurablePicardIteration
public import proofs.EndotacticPermanence.FiniteMinAC
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace EndotacticPermanence

open Filter Set MeasureTheory Metric ODE intervalIntegral
open scoped Topology NNReal

/-- Actual local AC solutions follow from measurable bounded Lipschitz fields.
The ODE holds almost everywhere; continuity of the rates is unnecessary. -/
theorem exists_local_ac_curve {d : ℕ} {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    {tmin tmax : ℝ} {t0 : Icc tmin tmax} {x0 : Fin d → ℝ} {a L K : NNReal}
    (hf : MeasurablePicardData f t0 x0 a L K) :
    ∃ x : ℝ → (Fin d → ℝ), x t0 = x0 ∧ LipschitzWith L x ∧
      AbsolutelyContinuousOnInterval x tmin tmax ∧
      MapsTo x (Icc tmin tmax) (closedBall x0 a) ∧
      (∀ᵐ t, t ∈ Ioo tmin tmax → HasDerivAt x (f t (x t)) t) ∧
      (∀ t ∈ Icc tmin tmax, x t = x0 + ∫ s in t0.val..t, f s (x s)) := by
  obtain ⟨α, hα⟩ := hf.exists_integral_solution_any_interval
  have horder : tmin ≤ tmax := t0.property.1.trans t0.property.2
  have hlip : LipschitzWith L α.compProj := by
    simpa only [mul_one] using! α.lipschitzWith.comp (LipschitzWith.projIcc horder)
  have heq (t : ℝ) (ht : t ∈ Icc tmin tmax) :
      α.compProj t = x0 + ∫ s in t0.val..t, f s (α.compProj s) := by
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact hα ⟨t, ht⟩
  have hint : IntervalIntegrable (fun s => f s (α.compProj s)) volume tmin tmax :=
    (hf.path_integrable α ⟨tmin, ⟨le_rfl, horder⟩⟩).symm.trans
      (hf.path_integrable α ⟨tmax, ⟨horder, le_rfl⟩⟩)
  have hcoord (i : Fin d) :
      IntervalIntegrable (fun s => f s (α.compProj s) i) volume tmin tmax :=
    ⟨(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).integrable_comp hint.1,
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).integrable_comp hint.2⟩
  have hderivs : ∀ᵐ t, ∀ i : Fin d, t ∈ uIcc tmin tmax →
      ∀ c ∈ uIcc tmin tmax,
        HasDerivAt (fun u => ∫ s in c..u, f s (α.compProj s) i)
          (f t (α.compProj t) i) t :=
    Filter.eventually_all.mpr (fun i => (hcoord i).ae_hasDerivAt_integral)
  refine ⟨α.compProj, ?_, hlip, hlip.lipschitzOnWith.absolutelyContinuousOnInterval,
    (fun t _ => α.compProj_mem_closedBall (by simpa using hf.time_bound)), ?_, heq⟩
  · rw [ODE.FunSpace.compProj_val]
    exact α.apply_of_zero
  · filter_upwards [hderivs] with t ht htint
    apply hasDerivAt_pi.mpr
    intro i
    have htu : t ∈ uIcc tmin tmax := by
      rw [uIcc_of_le horder]
      exact ⟨htint.1.le, htint.2.le⟩
    have ht0u : t0.val ∈ uIcc tmin tmax := by
      simpa only [uIcc_of_le horder] using t0.property
    have hi := (ht i htu t0 ht0u).const_add (x0 i)
    apply hi.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds htint.1 htint.2] with u hu
    have hucc : u ∈ Icc tmin tmax := ⟨hu.1.le, hu.2.le⟩
    have huint := hf.path_integrable α ⟨u, hucc⟩
    have he := congrFun (heq u hucc) i
    have hc := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm huint
    have hci : (∫ s in t0.val..u, f s (α.compProj s)) i =
        ∫ s in t0.val..u, f s (α.compProj s) i := hc.symm
    simp only [Pi.add_apply] at he
    rw [hci] at he
    exact he

end EndotacticPermanence
