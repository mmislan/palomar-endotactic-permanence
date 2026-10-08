module
public import proofs.EndotacticPermanence.CaratheodoryInterface
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

namespace EndotacticPermanence

open Set MeasureTheory Metric OAI.Problem326

/-- Integral Grönwall for actual AC curves; the measurable field need not
have pointwise time derivatives. The auxiliary integral has a continuous
integrand, allowing the library's pointwise Grönwall theorem to be used. -/
theorem integral_curves_dist_bound {d : ℕ}
    {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)} {C : Set (Fin d → ℝ)}
    (L : NNReal) {T : ℝ} (hT : 0 ≤ T)
    (hLip : ∀ t ∈ Icc 0 T, LipschitzOnWith L (f t) C)
    {x0 y0 : Fin d → ℝ} {x y : ℝ → (Fin d → ℝ)}
    (hx : IsForwardCaratheodoryCurve f x0 x)
    (hy : IsForwardCaratheodoryCurve f y0 y)
    (hxc : ∀ t ∈ Icc 0 T, x t ∈ C) (hyc : ∀ t ∈ Icc 0 T, y t ∈ C) :
    ∀ t ∈ Icc 0 T, dist (x t) (y t) ≤ dist x0 y0 * Real.exp ((L : ℝ) * t) := by
  let q : ℝ → ℝ := fun t => dist (x (projIcc 0 T hT t)) (y (projIcc 0 T hT t))
  have hxc0 : ContinuousOn x (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hx.2.2.1 T hT).continuousOn
  have hyc0 : ContinuousOn y (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hy.2.2.1 T hT).continuousOn
  have hq : Continuous q :=
    (hxc0.domRestrict.comp continuous_projIcc).dist (hyc0.domRestrict.comp continuous_projIcc)
  have hqeq (t : ℝ) (ht : t ∈ Icc 0 T) : q t = dist (x t) (y t) := by
    simp only [q, projIcc_of_mem hT ht]
  let U : ℝ → ℝ := fun t => dist x0 y0 + (L : ℝ) * ∫ s in (0 : ℝ)..t, q s
  have hU : Continuous U := by
    apply continuous_const.add
    exact continuous_const.mul
      (intervalIntegral.continuous_primitive (fun a b => hq.intervalIntegrable a b) 0)
  have hineq (t : ℝ) (ht : t ∈ Icc 0 T) : q t ≤ U t := by
    have hix := (hx.2.1 t ht.1).1
    have hiy := (hy.2.1 t ht.1).1
    have he : x t - y t = (x0 - y0) + ∫ s in (0 : ℝ)..t, (f s (x s) - f s (y s)) := by
      rw [(hx.2.1 t ht.1).2 t ⟨ht.1, le_rfl⟩,
        (hy.2.1 t ht.1).2 t ⟨ht.1, le_rfl⟩, intervalIntegral.integral_sub hix hiy]
      abel
    rw [hqeq t ht, dist_eq_norm, he]
    apply (norm_add_le _ _).trans
    change ‖x0 - y0‖ + ‖∫ s in (0 : ℝ)..t, (f s (x s) - f s (y s))‖ ≤
      ‖x0 - y0‖ + (L : ℝ) * ∫ s in (0 : ℝ)..t, q s
    apply add_le_add le_rfl
    apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    have hib : IntervalIntegrable (fun s => (L : ℝ) * q s) volume 0 t :=
      (continuous_const.mul hq).intervalIntegrable _ _
    have hi := intervalIntegral.integral_mono_on ht.1 (hix.sub hiy).norm hib
      (fun s hs => by
        have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
        simpa only [hqeq s hsT, dist_eq_norm] using
          (hLip s hsT).dist_le_mul (x s) (hxc s hsT) (y s) (hyc s hsT))
    simpa only [intervalIntegral.integral_const_mul] using hi
  have hUnonneg (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ U t :=
    (dist_nonneg : 0 ≤ q t).trans (hineq t ht)
  have hUd (t : ℝ) : HasDerivAt U ((L : ℝ) * q t) t := by
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hq.intervalIntegrable 0 t) hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
    exact (hd.const_mul (L : ℝ)).const_add (dist x0 y0)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    hU.continuousOn (fun t _ => (hUd t).hasDerivWithinAt)
    (a := 0) (b := T) (δ := dist x0 y0) (K := (L : ℝ)) (ε := 0)
    (by simp [U, Real.norm_eq_abs, abs_of_nonneg dist_nonneg])
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg L.coe_nonneg,
        abs_of_nonneg (dist_nonneg : 0 ≤ q t), Real.norm_eq_abs,
        abs_of_nonneg (hUnonneg t ⟨ht.1, ht.2.le⟩), add_zero]
      exact mul_le_mul_of_nonneg_left (hineq t ⟨ht.1, ht.2.le⟩) L.coe_nonneg)
  intro t ht
  have hg := hgr t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hUnonneg t ht), gronwallBound_ε0,
    sub_zero] at hg
  exact (hqeq t ht ▸ hineq t ht).trans hg

/-- One Lipschitz constant works for every boxed rate vector on a compact set. -/
theorem mass_action_uniform_lipschitz_compact {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℕ) (B : PositiveRateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) :
    ∃ L : NNReal, ∀ k, B.Contains k → LipschitzOnWith L
      (indexedMassAction source target k) C := by
  obtain ⟨A, hA⟩ := hC.exists_bound_of_continuousOn continuous_id.continuousOn
  let a : NNReal := ⟨max A 0, le_max_right _ _⟩
  have hsub : C ⊆ closedBall (0 : Fin d → ℝ) a := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact (hA x hx).trans (le_max_left A 0)
  obtain ⟨_, L, _, hL⟩ := uniform_mass_action_bounds source target B 0 a
  exact ⟨L, fun k hk => (hL k hk).mono hsub⟩

/-- Uniform initial-state stability on a compact invariant region. -/
theorem mass_action_continuous_dependence {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℕ) (B : PositiveRateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) :
    ∃ L : NNReal, 0 ≤ (L : ℝ) ∧ ∀ k : ℝ → R → ℝ,
      (∀ t, 0 ≤ t → B.Contains (k t)) →
      ∀ x0 y0 x y,
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x →
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) y0 y →
        (∀ t, 0 ≤ t → x t ∈ C) → (∀ t, 0 ≤ t → y t ∈ C) →
        ∀ t, 0 ≤ t → dist (x t) (y t) ≤ dist x0 y0 * Real.exp ((L : ℝ) * t) := by
  obtain ⟨L, hL⟩ := mass_action_uniform_lipschitz_compact source target B C hC
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro k hk x0 y0 x y hx hy hxc hyc t ht
  exact integral_curves_dist_bound L ht (fun s hs => hL (k s) (hk s hs.1))
    (forward_curve_iff_ac_ode.mpr hx) (forward_curve_iff_ac_ode.mpr hy)
    (fun s hs => hxc s hs.1) (fun s hs => hyc s hs.1) t ⟨ht, le_rfl⟩

end EndotacticPermanence
