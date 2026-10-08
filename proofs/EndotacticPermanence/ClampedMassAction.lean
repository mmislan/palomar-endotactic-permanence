module
public import proofs.EndotacticPermanence.MassActionRegularity
public import proofs.EndotacticPermanence.BoundedField
public import proofs.EndotacticPermanence.Imported.ClampExtension
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set MeasureTheory Metric Function
open scoped NNReal Topology

variable {d : ℕ} {R : Type*} [Fintype R]

noncomputable def clampedMassAction (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (a b : Fin d → ℝ) (hab : a ≤ b) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  indexedMassAction source target
    (coordinateClamp B.lower B.upper B.lower_le_upper (k t))
    (coordinateClamp a b hab x)

theorem clamped_mass_action_eq (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (a b : Fin d → ℝ) (hab : a ≤ b) {t : ℝ} {x : Fin d → ℝ}
    (hk : B.Contains (k t)) (hx : x ∈ Icc a b) :
    clampedMassAction source target B k a b hab t x =
      indexedMassAction source target (k t) x := by
  unfold clampedMassAction
  rw [coordinateClamp_eq_self hab hx,
    coordinateClamp_eq_self B.lower_le_upper
      (show k t ∈ Icc B.lower B.upper from
        ⟨fun e => (hk e).1, fun e => (hk e).2⟩)]

theorem exists_bounded_clamped_field (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (k : ℝ → R → ℝ)
    (hk : ∀ e, Measurable (fun t => k t e))
    (a b : Fin d → ℝ) (hab : a ≤ b) :
    Nonempty (BoundedTimeField d (clampedMassAction source target B k a b hab)) := by
  let C : Set ((R → ℝ) × (Fin d → ℝ)) := Icc B.lower B.upper ×ˢ Icc a b
  have hcompact : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hconvex : Convex ℝ C := (convex_Icc B.lower B.upper).prod (convex_Icc a b)
  have hdiff := contDiff_indexed_mass_action source target
  obtain ⟨K, hK⟩ := hdiff.contDiffOn.exists_lipschitzOnWith (by norm_num) hconvex hcompact
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hdiff.continuous.continuousOn
  let L : NNReal := ⟨max M 0, le_max_right _ _⟩
  let kr := fun t => coordinateClamp B.lower B.upper B.lower_le_upper (k t)
  have hkr : Measurable kr :=
    (coordinateClamp_lipschitz B.lower B.upper B.lower_le_upper).continuous.measurable.comp
      (Measurable.of_eval hk)
  have hkrmem (t : ℝ) : kr t ∈ Icc B.lower B.upper :=
    coordinateClamp_mem B.lower B.upper B.lower_le_upper (k t)
  refine ⟨⟨L, K, ?_, ?_, ?_⟩⟩
  · have hfield := measurable_indexed_mass_action source target kr
      (fun e => (measurable_pi_apply e).comp hkr)
    exact hfield.comp (measurable_fst.prodMk
      ((coordinateClamp_lipschitz a b hab).continuous.measurable.comp measurable_snd))
  · intro t
    have hf : LipschitzOnWith K (indexedMassAction source target (kr t)) (Icc a b) := by
      intro x hx y hy
      have hh := hK (show (kr t, x) ∈ C from ⟨hkrmem t, hx⟩)
        (show (kr t, y) ∈ C from ⟨hkrmem t, hy⟩)
      simpa only [Prod.edist_eq, edist_self, max_eq_right zero_le] using hh
    have hg := hf.comp (coordinateClamp_lipschitz a b hab).lipschitzOnWith
      (show MapsTo (coordinateClamp a b hab) univ (Icc a b) from
        fun x _ => coordinateClamp_mem a b hab x)
    simpa only [mul_one] using! lipschitzOnWith_univ.mp hg
  · intro t x
    exact (hM (kr t, coordinateClamp a b hab x)
      ⟨hkrmem t, coordinateClamp_mem a b hab x⟩).trans (le_max_left M 0)

end EndotacticPermanence
