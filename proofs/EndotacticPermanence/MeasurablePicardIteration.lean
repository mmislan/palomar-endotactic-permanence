module
public import proofs.EndotacticPermanence.MeasurablePicard
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace EndotacticPermanence

open Function intervalIntegral MeasureTheory Metric Set ODE
open scoped Nat NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t0 : Icc tmin tmax}
  {x0 : E} {a L K : NNReal}

namespace MeasurablePicardData

/-- The factorial estimate uses integrability, not time continuity. -/
theorem dist_iterate_next_apply_le (hf : MeasurablePicardData f t0 x0 a L K)
    (α β : ODE.FunSpace t0 x0 0 L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((hf.next)^[n] α t) ((hf.next)^[n] β t) ≤
      (K * |t.val - t0.val|) ^ n / n.factorial * dist α β := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := α.toContinuousMap) (g := β.toContinuousMap) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm]
    change ‖picard f t0 x0 ((hf.next)^[n] α).compProj t -
      picard f t0 x0 ((hf.next)^[n] β).compProj t‖ ≤ _
    rw [picard_apply, picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hf.path_integrable _ t) (hf.path_integrable _ t)]
    calc
      _ ≤ ∫ s in uIoc t0.val t.val,
          K ^ (n + 1) * |s - t0| ^ n / n.factorial * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        have hst : s ∈ Icc tmin tmax :=
          (uIcc_subset_Icc t0.property t.property) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, ODE.FunSpace.compProj_of_mem hst,
          ODE.FunSpace.compProj_of_mem hst]
        calc
          _ ≤ K * dist ((hf.next)^[n] α ⟨s, hst⟩) ((hf.next)^[n] β ⟨s, hst⟩) :=
            (hf.lipschitz s hst).dist_le_mul _
              (ODE.FunSpace.mem_closedBall (by simpa using hf.time_bound)) _
              (ODE.FunSpace.mem_closedBall (by simpa using hf.time_bound))
          _ ≤ K ^ (n + 1) * |s - t0| ^ n / n.factorial * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [← mul_pow] using hn ⟨s, hst⟩
      _ ≤ (K * |t.val - t0.val|) ^ (n + 1) / (n + 1).factorial * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem dist_iterate_next_le (hf : MeasurablePicardData f t0 x0 a L K)
    (α β : ODE.FunSpace t0 x0 0 L) (n : ℕ) :
    dist ((hf.next)^[n] α) ((hf.next)^[n] β) ≤
      (K * max (tmax - t0) (t0 - tmin)) ^ n / n.factorial * dist α β := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply (hf.dist_iterate_next_apply_le α β n t).trans
    gcongr
    exact abs_sub_le_max_sub t.property.1 t.property.2 t0.val
  · have hspan : 0 ≤ max (tmax - t0) (t0 - tmin) :=
      le_max_of_le_left (sub_nonneg.mpr t0.property.2)
    positivity

theorem exists_contracting_iterate (hf : MeasurablePicardData f t0 x0 a L K) :
    ∃ n : ℕ, ∃ C : NNReal, ContractingWith C (hf.next)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop
    (K * max (tmax - t0) (t0 - tmin)) |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hspan : 0 ≤ max (tmax - t0) (t0 - tmin) :=
    le_max_of_le_left (sub_nonneg.mpr t0.property.2)
  have hpos : 0 ≤ (K * max (tmax - t0) (t0 - tmin)) ^ n / n.factorial := by positivity
  refine ⟨n, ⟨_, hpos⟩, hn, LipschitzWith.of_dist_le_mul (fun α β => ?_)⟩
  exact hf.dist_iterate_next_le α β n

theorem exists_integral_solution_any_interval [CompleteSpace E]
    (hf : MeasurablePicardData f t0 x0 a L K) :
    ∃ α : ODE.FunSpace t0 x0 0 L,
      ∀ t : Icc tmin tmax, α t = x0 + ∫ s in t0.val..t.val, f s (α.compProj s) := by
  obtain ⟨n, C, hctr⟩ := hf.exists_contracting_iterate
  let α : ODE.FunSpace t0 x0 0 L := hctr.fixedPoint ((hf.next)^[n])
  have hfix : IsFixedPt hf.next α := hctr.isFixedPt_fixedPoint_iterate
  refine ⟨α, fun t => ?_⟩
  exact (congrArg (fun γ : ODE.FunSpace t0 x0 0 L => γ t) hfix).symm

end MeasurablePicardData
end EndotacticPermanence
