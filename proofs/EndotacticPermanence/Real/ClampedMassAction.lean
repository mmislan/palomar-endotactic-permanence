module
public import proofs.EndotacticPermanence.Real.PositiveRegularity
public import proofs.EndotacticPermanence.BoundedField
public import proofs.EndotacticPermanence.Imported.ClampExtension

@[expose] public section

namespace EndotacticPermanence.RealComplex

open OAI.Problem326 Set MeasureTheory Metric Function
open scoped NNReal Topology

noncomputable section
variable {d : ℕ} {R : Type*} [Fintype R]

def clampedMassAction (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (a b : Fin d → ℝ) (hab : a ≤ b) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  indexedMassAction source target
    (coordinateClamp B.lower B.upper B.lower_le_upper (k t)) (coordinateClamp a b hab x)

theorem clamped_mass_action_eq (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (a b : Fin d → ℝ) (hab : a ≤ b) {t : ℝ} {x : Fin d → ℝ}
    (hk : B.Contains (k t)) (hx : x ∈ Icc a b) :
    clampedMassAction source target B k a b hab t x = indexedMassAction source target (k t) x := by
  unfold clampedMassAction
  rw [coordinateClamp_eq_self hab hx, coordinateClamp_eq_self B.lower_le_upper
    (show k t ∈ Icc B.lower B.upper from ⟨fun e => (hk e).1, fun e => (hk e).2⟩)]

theorem exists_bounded_clamped_field (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e))
    (a b : Fin d → ℝ) (hab : a ≤ b) (ha : ∀ i, 0 < a i) :
    Nonempty (BoundedTimeField d (clampedMassAction source target B k a b hab)) := by
  obtain ⟨L, K, hbound, hLip⟩ := uniform_mass_action_bounds_box source target B a b ha
  let kr := fun t => coordinateClamp B.lower B.upper B.lower_le_upper (k t)
  have hkr : Measurable kr :=
    (coordinateClamp_lipschitz B.lower B.upper B.lower_le_upper).continuous.measurable.comp
      (Measurable.of_eval hk)
  have hkrbox (t : ℝ) : B.Contains (kr t) := by
    have hm := coordinateClamp_mem B.lower B.upper B.lower_le_upper (k t)
    exact fun e => ⟨hm.1 e, hm.2 e⟩
  refine ⟨⟨L, K, ?_, ?_, ?_⟩⟩
  · have hfield := measurable_indexed_mass_action source target kr
      (fun e => (measurable_pi_apply e).comp hkr)
    exact hfield.comp (measurable_fst.prodMk
      ((coordinateClamp_lipschitz a b hab).continuous.measurable.comp measurable_snd))
  · intro t
    have hg := (hLip (kr t) (hkrbox t)).comp (coordinateClamp_lipschitz a b hab).lipschitzOnWith
      (show MapsTo (coordinateClamp a b hab) univ (Icc a b) from
        fun x _ => coordinateClamp_mem a b hab x)
    simpa only [mul_one] using! lipschitzOnWith_univ.mp hg
  · intro t x
    exact hbound (kr t) (hkrbox t) _ (coordinateClamp_mem a b hab x)

end
end EndotacticPermanence.RealComplex
