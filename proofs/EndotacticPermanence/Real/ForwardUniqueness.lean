module
public import proofs.EndotacticPermanence.Real.EndotacticTrapping

@[expose] public section

namespace EndotacticPermanence.RealComplex

open OAI.Problem326 Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

/-- Positive curves admit a common positive compact enclosure on every finite
time interval. No boundary smoothness or bound uniform in all time is assumed. -/
theorem forward_mass_action_unique (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e))
    (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    {x0 : Fin d → ℝ} {x y : ℝ → (Fin d → ℝ)}
    (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x)
    (hy : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 y)
    (hxpos : ∀ t : ℝ, 0 ≤ t → PositiveState (x t))
    (hypos : ∀ t : ℝ, 0 ≤ t → PositiveState (y t)) : EqOn x y (Ici 0) := by
  intro T hT
  change 0 ≤ T at hT
  have hcx : ContinuousOn x (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hx.2.2.1 T hT).continuousOn
  have hcy : ContinuousOn y (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hy.2.2.1 T hT).continuousOn
  let C : Set (Fin d → ℝ) := x '' Icc 0 T ∪ y '' Icc 0 T
  have hC : IsCompact C :=
    (isCompact_Icc.image_of_continuousOn hcx).union (isCompact_Icc.image_of_continuousOn hcy)
  have hCpos : ∀ z ∈ C, PositiveState z := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨t, ht, rfl⟩ := hz
      exact hxpos t ht.1
    · obtain ⟨t, ht, rfl⟩ := hz
      exact hypos t ht.1
  obtain ⟨a, b, ha, hab, hsub⟩ := compact_positive_box hC hCpos
  let f := clampedMassAction source target B k a b hab
  obtain ⟨F⟩ := exists_bounded_clamped_field source target B k hk a b hab ha
  have hxb (t : ℝ) (ht : t ∈ Icc 0 T) : x t ∈ Icc a b :=
    hsub (Or.inl (mem_image_of_mem x ht))
  have hyb (t : ℝ) (ht : t ∈ Icc 0 T) : y t ∈ Icc a b :=
    hsub (Or.inr (mem_image_of_mem y ht))
  have lift (z : ℝ → (Fin d → ℝ))
      (hz : IsIntegralCurveOn (fun t => indexedMassAction source target (k t)) x0 T z)
      (hzb : ∀ t ∈ Icc 0 T, z t ∈ Icc a b) : IsIntegralCurveOn f x0 T z := by
    have heq (t : ℝ) (ht : t ∈ Icc 0 T) :
        indexedMassAction source target (k t) (z t) = f t (z t) :=
      (clamped_mass_action_eq source target B k a b hab (hkbox t ht.1) (hzb t ht)).symm
    refine ⟨hz.1.congr_ae ?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      apply heq
      simpa only [uIcc_of_le hT] using uIoc_subset_uIcc ht
    · intro t ht
      rw [hz.2 t ht]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      exact heq u (uIcc_subset_Icc ⟨le_rfl, hT⟩ ht hu)
  exact F.integral_curve_unique hT (lift x (hx.2.1 T hT) hxb)
    (lift y (hy.2.1 T hT) hyb) ⟨hT, le_rfl⟩

end EndotacticPermanence.RealComplex
