module
public import proofs.EndotacticPermanence.CaratheodoryCurve

@[expose] public section

namespace EndotacticPermanence

open Filter Set MeasureTheory Metric ODE intervalIntegral Function
open scoped NNReal Topology

/-- Global field bounds will be proved for the clamped mass-action field. -/
structure BoundedTimeField (d : ℕ) (f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)) where
  bound : NNReal
  lip : NNReal
  measurable : Measurable (Function.uncurry f)
  lipschitz : ∀ t, LipschitzWith lip (f t)
  norm_le : ∀ t x, ‖f t x‖ ≤ bound

def IsIntegralCurveOn {d : ℕ} (f : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (x0 : Fin d → ℝ) (T : ℝ) (x : ℝ → (Fin d → ℝ)) : Prop :=
  IntervalIntegrable (fun t => f t (x t)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, x t = x0 + ∫ s in (0 : ℝ)..t, f s (x s)

namespace BoundedTimeField

variable {d : ℕ} {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}

theorem picardData (F : BoundedTimeField d f) (x0 : Fin d → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    MeasurablePicardData f (⟨0, ⟨le_rfl, hT⟩⟩ : Icc 0 T) x0
      (F.bound * ⟨T, hT⟩) F.bound F.lip where
  measurable := F.measurable
  lipschitz := fun t _ => (F.lipschitz t).lipschitzOnWith
  norm_le := fun t _ x _ => F.norm_le t x
  time_bound := by
    change (F.bound : ℝ) * max (T - 0) (0 - 0) ≤ (F.bound : ℝ) * T
    simp [max_eq_left hT]

theorem exists_integral_curve (F : BoundedTimeField d f) (x0 : Fin d → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → (Fin d → ℝ), IsIntegralCurveOn f x0 T x ∧
      x 0 = x0 ∧ AbsolutelyContinuousOnInterval x 0 T ∧
      (∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (f t (x t)) t) := by
  let H := F.picardData x0 hT
  obtain ⟨x, hx0, hlip, hac, hmaps, hode, heq⟩ := exists_local_ac_curve H
  have hxint : IntervalIntegrable (fun s => f s (x s)) volume 0 T := by
    apply intervalIntegrable_iff.mpr
    apply Measure.integrableOn_of_bounded (by exact measure_Ioc_lt_top.ne)
      ((F.measurable.comp (measurable_id.prodMk hlip.continuous.measurable)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun t => F.norm_le t (x t))
  exact ⟨x, ⟨hxint, heq⟩, hx0, hac, hode⟩

theorem integral_curve_lipschitz (F : BoundedTimeField d f)
    {x0 : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)} (hT : 0 ≤ T)
    (hx : IsIntegralCurveOn f x0 T x) : LipschitzOnWith F.bound x (Icc 0 T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hint (u : ℝ) (hu : u ∈ Icc 0 T) :
      IntervalIntegrable (fun s => f s (x s)) volume 0 u := by
    apply hx.1.mono_set
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ⟨le_rfl, hT⟩ hu
  rw [hx.2 s hs, hx.2 t ht, dist_eq_norm, add_sub_add_left_eq_sub,
    integral_interval_sub_left
      (hint s hs) (hint t ht), Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => F.norm_le u (x u))

end BoundedTimeField

theorem IsIntegralCurveOn.mono {d : ℕ}
    {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)} {x0 : Fin d → ℝ}
    {T U : ℝ} {x : ℝ → (Fin d → ℝ)} (hx : IsIntegralCurveOn f x0 U x)
    (hT : 0 ≤ T) (hTU : T ≤ U) : IsIntegralCurveOn f x0 T x := by
  refine ⟨hx.1.mono_set ?_, fun t ht => hx.2 t ⟨ht.1, ht.2.trans hTU⟩⟩
  rw [uIcc_of_le hT, uIcc_of_le (hT.trans hTU)]
  exact Icc_subset_Icc_right hTU

namespace BoundedTimeField

theorem integral_curve_unique (F : BoundedTimeField d f)
    {x0 : Fin d → ℝ} {T : ℝ} {x y : ℝ → (Fin d → ℝ)} (hT : 0 ≤ T)
    (hx : IsIntegralCurveOn f x0 T x) (hy : IsIntegralCurveOn f x0 T y) :
    EqOn x y (Icc 0 T) := by
  let t0 : Icc 0 T := ⟨0, ⟨le_rfl, hT⟩⟩
  let H := F.picardData x0 hT
  have lift (z : ℝ → (Fin d → ℝ)) (hz : IsIntegralCurveOn f x0 T z) :
      ∃ α : ODE.FunSpace t0 x0 0 F.bound,
        (∀ t : Icc 0 T, α t = z t) ∧ IsFixedPt H.next α := by
    have hz0 : z 0 = x0 := by simpa using hz.2 0 ⟨le_rfl, hT⟩
    let α : ODE.FunSpace t0 x0 0 F.bound :=
      { toFun := fun t => z t
        lipschitzWith := fun s t => by
          simpa only [Subtype.edist_eq] using
            (F.integral_curve_lipschitz hT hz) s.property t.property
        mem_closedBall₀ := by simp [t0, hz0] }
    refine ⟨α, fun _ => rfl, ?_⟩
    apply ODE.FunSpace.ext
    intro t
    change x0 + ∫ s in (0 : ℝ)..t.val, f s (α.compProj s) = z t.val
    rw [hz.2 t.val t.property]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsT : s ∈ Icc 0 T := uIcc_subset_Icc t0.property t.property hs
    change f s (α.compProj s) = f s (z s)
    rw [ODE.FunSpace.compProj_of_mem hsT]
  obtain ⟨α, hα, hfixα⟩ := lift x hx
  obtain ⟨β, hβ, hfixβ⟩ := lift y hy
  obtain ⟨n, C, hctr⟩ := H.exists_contracting_iterate
  have hab : α = β := hctr.fixedPoint_unique' (hfixα.iterate n) (hfixβ.iterate n)
  intro t ht
  exact (hα ⟨t, ht⟩).symm.trans (hab ▸ hβ ⟨t, ht⟩)

end BoundedTimeField
end EndotacticPermanence
