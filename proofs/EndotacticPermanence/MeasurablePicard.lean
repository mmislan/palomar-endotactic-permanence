module
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace EndotacticPermanence

open Function intervalIntegral MeasureTheory Metric Set ODE
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Local measurable-field hypotheses. No solution or global bound is assumed. -/
structure MeasurablePicardData (f : ℝ → E → E) {tmin tmax : ℝ}
    (t0 : Icc tmin tmax) (x0 : E) (a L K : NNReal) : Prop where
  measurable : Measurable (Function.uncurry f)
  lipschitz : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x0 a)
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x0 a, ‖f t x‖ ≤ L
  time_bound : L * max (tmax - t0) (t0 - tmin) ≤ a

namespace MeasurablePicardData

variable {f : ℝ → E → E} {tmin tmax : ℝ} {t0 : Icc tmin tmax}
  {x0 : E} {a L K : NNReal}

omit [NormedSpace ℝ E] in
theorem path_integrable (hf : MeasurablePicardData f t0 x0 a L K)
    (α : ODE.FunSpace t0 x0 0 L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun s => f s (α.compProj s)) volume t0 t := by
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (by exact measure_Ioc_lt_top.ne)
    ((hf.measurable.comp (measurable_id.prodMk α.continuous_compProj.measurable)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  have hst : s ∈ Icc tmin tmax :=
    (uIcc_subset_Icc t0.property t.property) (uIoc_subset_uIcc hs)
  exact hf.norm_le s hst _ (α.compProj_mem_closedBall (by simpa using hf.time_bound))

noncomputable def next (hf : MeasurablePicardData f t0 x0 a L K)
    (α : ODE.FunSpace t0 x0 0 L) : ODE.FunSpace t0 x0 0 L where
  toFun t := ODE.picard f t0 x0 α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t1 t2 => by
    rw [dist_eq_norm, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left (hf.path_integrable α t1) (hf.path_integrable α t2),
      Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hst : s ∈ Icc tmin tmax :=
      (uIcc_subset_Icc t2.property t1.property) (uIoc_subset_uIcc hs)
    exact hf.norm_le s hst _ (α.compProj_mem_closedBall (by simpa using hf.time_bound))
  mem_closedBall₀ := by simp

theorem next_dist_le (hf : MeasurablePicardData f t0 x0 a L K)
    (α β : ODE.FunSpace t0 x0 0 L) :
    dist (hf.next α) (hf.next β) ≤
      (K : ℝ) * max (tmax - t0) (t0 - tmin) * dist α β := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    change dist (picard f t0 x0 α.compProj t) (picard f t0 x0 β.compProj t) ≤ _
    rw [dist_eq_norm, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hf.path_integrable α t) (hf.path_integrable β t)]
    calc
      _ ≤ ((K : ℝ) * dist α β) * |t.val - t0.val| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        have hst : s ∈ Icc tmin tmax :=
          (uIcc_subset_Icc t0.property t.property) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, ODE.FunSpace.compProj_of_mem hst,
          ODE.FunSpace.compProj_of_mem hst]
        apply (hf.lipschitz s hst).dist_le_mul _
          (ODE.FunSpace.mem_closedBall (by simpa using hf.time_bound)) _
          (ODE.FunSpace.mem_closedBall (by simpa using hf.time_bound)) |>.trans
        exact mul_le_mul_of_nonneg_left
          (ContinuousMap.dist_apply_le_dist (f := α.toContinuousMap)
            (g := β.toContinuousMap) ⟨s, hst⟩) K.coe_nonneg
      _ ≤ (K : ℝ) * max (tmax - t0) (t0 - tmin) * dist α β := by
        have hspan := abs_sub_le_max_sub t.property.1 t.property.2 t0.val
        calc
          _ ≤ ((K : ℝ) * dist α β) * max (tmax - t0) (t0 - tmin) :=
            mul_le_mul_of_nonneg_left hspan (mul_nonneg K.coe_nonneg dist_nonneg)
          _ = _ := by ring
  · exact mul_nonneg (mul_nonneg K.coe_nonneg
      (le_max_of_le_left (sub_nonneg.mpr t0.property.2))) dist_nonneg

/-- Banach's theorem supplies the actual integral solution for a measurable field. -/
theorem exists_integral_solution [CompleteSpace E]
    (hf : MeasurablePicardData f t0 x0 a L K)
    (hsmall : (K : ℝ) * max (tmax - t0) (t0 - tmin) < 1) :
    ∃ α : ODE.FunSpace t0 x0 0 L,
      ∀ t : Icc tmin tmax, α t = x0 + ∫ s in t0.val..t.val, f s (α.compProj s) := by
  have hspan : 0 ≤ max (tmax - t0) (t0 - tmin) :=
    le_max_of_le_left (sub_nonneg.mpr t0.property.2)
  let C : NNReal := ⟨(K : ℝ) * max (tmax - t0) (t0 - tmin),
    mul_nonneg K.coe_nonneg hspan⟩
  have hC : (C : ℝ) = (K : ℝ) * max (tmax - t0) (t0 - tmin) := by
    rfl
  have hctr : ContractingWith C hf.next := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun α β => ?_)⟩
    · exact_mod_cast (hC ▸ hsmall)
    · rw [hC]
      exact hf.next_dist_le α β
  let α := hctr.fixedPoint hf.next
  refine ⟨α, fun t => ?_⟩
  have hfix : hf.next α = α := hctr.fixedPoint_isFixedPt
  exact (congrArg (fun γ : ODE.FunSpace t0 x0 0 L => γ t) hfix).symm

end MeasurablePicardData
end EndotacticPermanence
