module
public import proofs.EndotacticPermanence.ObservableDynamics
public import proofs.EndotacticPermanence.ClassPreservation
public import proofs.EndotacticPermanence.GlobalBoundedCurve
public import proofs.EndotacticPermanence.EndotacticBarrier
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set Filter MeasureTheory
open scoped Topology

variable {d : ℕ} {R : Type*} [Fintype R]

def IsForwardCaratheodoryCurve (f : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (x0 : Fin d → ℝ) (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    (∀ T : ℝ, 0 ≤ T → IsIntegralCurveOn f x0 T x) ∧
    (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval x 0 T) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (f t (x t)) t)

/-- A geometric plateau produces an actual global mass-action curve.
Global existence and boundedness are conclusions of the clamped construction. -/
theorem exists_trapped_mass_action_curve (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (G : GeometricFamily d (sourceComparisons source))
    (c : Fin d → ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    {j0 : Fin G.n} {K : Set (Fin d → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hz : G.slope j0 = 0)
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0)
    (hKB : K ⊆ interior (Icc (fun _ => h) (fun _ => h⁻¹)))
    (hmargin : ∀ x ∈ positiveClass source target c,
      x ∈ Icc (fun _ => h) (fun _ => h⁻¹) → x ∉ K →
        ∀ j, AffineActive G.slope (fun k => G.offset k h) x j →
          ∀ k : R → ℝ, B.Contains k →
            δ ≤ dot (G.slope j) (indexedMassAction source target k x))
    (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e))
    (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    (x0 : Fin d → ℝ) (hx0K : x0 ∈ K)
    (hx0S : x0 - c ∈ stoichiometricSubspace source target) :
    ∃ x : ℝ → (Fin d → ℝ),
      IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x ∧
      (∀ t : ℝ, 0 ≤ t → x t ∈ K) ∧
      (∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c) := by
  have hab : (fun _ : Fin d => h) ≤ (fun _ => h⁻¹) := by
    intro i
    rw [inv_eq_one_div, le_div_iff₀ hh]
    nlinarith
  let f := clampedMassAction source target B k (fun _ => h) (fun _ => h⁻¹) hab
  obtain ⟨F⟩ := exists_bounded_clamped_field source target B k hk
    (fun _ => h) (fun _ => h⁻¹) hab
  obtain ⟨x, hx0, hint, hac, hode⟩ := F.exists_global_curve x0
  have hclass := clamped_integral_curve_in_class source target B k
    (fun _ => h) (fun _ => h⁻¹) hab hx0S hint
  have htrapped (T : ℝ) (hT : 0 ≤ T) : MapsTo x (Icc 0 T) K := by
    apply G.trapped_by_plateau h hz hK hKB isClosed_Icc hT (hac T hT)
      (by rwa [hx0])
    intro τ hτ hseg
    filter_upwards [hode τ hτ.1, volume.ae_ne 0, volume.ae_ne τ] with t ht hn0 hnτ htmem hnot j hj
    have hti : t ∈ Ioo 0 τ :=
      ⟨lt_of_le_of_ne htmem.1 (Ne.symm hn0), lt_of_le_of_ne htmem.2 hnτ⟩
    have hxbox := hseg htmem
    have hxclass : x t ∈ positiveClass source target c :=
      ⟨fun i => hh.trans_le (hxbox.1 i), hclass t htmem.1⟩
    have heq := clamped_mass_action_eq source target B k
      (fun _ => h) (fun _ => h⁻¹) hab (hkbox t htmem.1) hxbox
    have hd := ht hti
    rw [heq] at hd
    rw [(affine_branch_hasDerivAt (G.slope j) (G.offset j h) hd).deriv]
    exact hδ.le.trans (hmargin (x t) hxclass hxbox hnot j hj (k t) (hkbox t htmem.1))
  have hKall (t : ℝ) (ht : 0 ≤ t) : x t ∈ K := htrapped t ht ⟨ht, le_rfl⟩
  have heq (t : ℝ) (ht : 0 ≤ t) : f t (x t) = indexedMassAction source target (k t) (x t) :=
    clamped_mass_action_eq source target B k (fun _ => h) (fun _ => h⁻¹) hab
      (hkbox t ht) (interior_subset (hKB (hKall t ht)))
  refine ⟨x, ⟨hx0, ?_, hac, ?_⟩, hKall, ?_⟩
  · intro T hT
    refine ⟨(hint T hT).1.congr_ae ?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have ht0 : 0 ≤ t := by
        have hhT : t ∈ Icc 0 T := by
          simpa only [uIcc_of_le hT] using uIoc_subset_uIcc ht
        exact hhT.1
      exact heq t ht0
    · intro t ht
      rw [(hint T hT).2 t ht]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := by
        rw [uIcc_of_le ht.1] at hu
        exact hu.1
      exact heq u hu0
  · intro T hT
    filter_upwards [hode T hT] with t ht htmem
    have hd := ht htmem
    change HasDerivAt x (f t (x t)) t at hd
    rwa [heq t htmem.1.le] at hd
  · intro t ht
    have hxbox := interior_subset (hKB (hKall t ht))
    exact ⟨fun i => hh.trans_le (hxbox.1 i), hclass t ht⟩

end EndotacticPermanence
