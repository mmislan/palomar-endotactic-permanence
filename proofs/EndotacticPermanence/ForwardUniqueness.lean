module
public import proofs.EndotacticPermanence.EndotacticTrapping
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

theorem forward_mass_action_unique (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (hk : ∀ e, Measurable (fun t => k t e))
    (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    {x0 : Fin d → ℝ} {x y : ℝ → (Fin d → ℝ)}
    (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x)
    (hy : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 y) :
    EqOn x y (Ici 0) := by
  intro T hT
  change 0 ≤ T at hT
  have hcx : ContinuousOn x (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hx.2.2.1 T hT).continuousOn
  have hcy : ContinuousOn y (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hy.2.2.1 T hT).continuousOn
  obtain ⟨Mx, hMx⟩ := isCompact_Icc.exists_bound_of_continuousOn hcx
  obtain ⟨My, hMy⟩ := isCompact_Icc.exists_bound_of_continuousOn hcy
  let M := max 0 (max Mx My)
  have hM : 0 ≤ M := le_max_left _ _
  have hab : (fun _ : Fin d => -M) ≤ (fun _ => M) := fun _ => by linarith
  let f := clampedMassAction source target B k (fun _ => -M) (fun _ => M) hab
  obtain ⟨F⟩ := exists_bounded_clamped_field source target B k hk
    (fun _ => -M) (fun _ => M) hab
  have hxb (t : ℝ) (ht : t ∈ Icc 0 T) : x t ∈ Icc (fun _ => -M) (fun _ => M) := by
    have hn : ‖x t‖ ≤ M := (hMx t ht).trans ((le_max_left Mx My).trans (le_max_right 0 _))
    have hi (i : Fin d) : |x t i| ≤ M := (norm_le_pi_norm (x t) i).trans hn
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  have hyb (t : ℝ) (ht : t ∈ Icc 0 T) : y t ∈ Icc (fun _ => -M) (fun _ => M) := by
    have hn : ‖y t‖ ≤ M := (hMy t ht).trans ((le_max_right Mx My).trans (le_max_right 0 _))
    have hi (i : Fin d) : |y t i| ≤ M := (norm_le_pi_norm (y t) i).trans hn
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  have lift (z : ℝ → (Fin d → ℝ))
      (hz : IsIntegralCurveOn (fun t => indexedMassAction source target (k t)) x0 T z)
      (hzb : ∀ t ∈ Icc 0 T, z t ∈ Icc (fun _ => -M) (fun _ => M)) :
      IsIntegralCurveOn f x0 T z := by
    have heq (t : ℝ) (ht : t ∈ Icc 0 T) :
        indexedMassAction source target (k t) (z t) = f t (z t) :=
      (clamped_mass_action_eq source target B k _ _ hab (hkbox t ht.1) (hzb t ht)).symm
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

end EndotacticPermanence
