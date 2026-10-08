module
public import proofs.EndotacticPermanence.Real.PositiveRegularity
public import proofs.EndotacticPermanence.ContinuousDependence
public import proofs.EndotacticPermanence.AlmostEverywhereRates

@[expose] public section

namespace EndotacticPermanence.RealComplex

open Set MeasureTheory Metric OAI.Problem326

/-- One Lipschitz constant on a compact positive set, uniform over boxed rates. -/
theorem mass_action_uniform_lipschitz_compact {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℝ) (B : PositiveRateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) (hpos : ∀ x ∈ C, PositiveState x) :
    ∃ L : NNReal, ∀ k, B.Contains k → LipschitzOnWith L
      (indexedMassAction source target k) C := by
  obtain ⟨a, b, ha, _, hsub⟩ := compact_positive_box hC hpos
  obtain ⟨_, L, _, hL⟩ := uniform_mass_action_bounds_box source target B a b ha
  exact ⟨L, fun k hk => (hL k hk).mono hsub⟩

/-- Stability with respect to initial data for the same pointwise admissible
history, when both curves stay in a common compact positive region. -/
theorem mass_action_continuous_dependence {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℝ) (B : PositiveRateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) (hpos : ∀ x ∈ C, PositiveState x) :
    ∃ L : NNReal, 0 ≤ (L : ℝ) ∧ ∀ k : ℝ → R → ℝ,
      (∀ t, 0 ≤ t → B.Contains (k t)) → ∀ x0 y0 x y,
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x →
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) y0 y →
        (∀ t, 0 ≤ t → x t ∈ C) → (∀ t, 0 ≤ t → y t ∈ C) →
        ∀ t, 0 ≤ t → dist (x t) (y t) ≤ dist x0 y0 * Real.exp ((L : ℝ) * t) := by
  obtain ⟨L, hL⟩ := mass_action_uniform_lipschitz_compact source target B C hC hpos
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro k hk x0 y0 x y hx hy hxc hyc t ht
  exact integral_curves_dist_bound L ht (fun s hs => hL (k s) (hk s hs.1))
    (forward_curve_iff_ac_ode.mpr hx) (forward_curve_iff_ac_ode.mpr hy)
    (fun s hs => hxc s hs.1) (fun s hs => hyc s hs.1) t ⟨ht, le_rfl⟩

/-- The same initial-data estimate for a.e. admissible rate histories.
The Lipschitz constant is selected before the history and its null-set repair. -/
theorem mass_action_continuous_dependence_ae {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℝ) (B : PositiveRateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) (hpos : ∀ x ∈ C, PositiveState x) :
    ∃ L : NNReal, 0 ≤ (L : ℝ) ∧ ∀ k : ℝ → R → ℝ,
      AEAdmissible B k → ∀ x0 y0 x y,
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x →
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) y0 y →
        (∀ t, 0 ≤ t → x t ∈ C) → (∀ t, 0 ≤ t → y t ∈ C) →
        ∀ t, 0 ≤ t → dist (x t) (y t) ≤ dist x0 y0 * Real.exp ((L : ℝ) * t) := by
  obtain ⟨L, hL, hbound⟩ := mass_action_continuous_dependence source target B C hC hpos
  refine ⟨L, hL, ?_⟩
  intro k hk x0 y0 x y hx hy hxc hyc t ht
  obtain ⟨kr, _, hkrb, heq⟩ := repair_rate_history B k hk
  have hf : ∀ᵐ u ∂forwardVolume, ∀ z,
      indexedMassAction source target (k u) z = indexedMassAction source target (kr u) z := by
    filter_upwards [heq] with u hu
    intro z
    rw [hu]
  exact hbound kr (fun u _ => hkrb u) x0 y0 x y
    ((caratheodory_solution_congr_forward_ae hf).mp hx)
    ((caratheodory_solution_congr_forward_ae hf).mp hy) hxc hyc t ht

end EndotacticPermanence.RealComplex
