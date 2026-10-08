module
public import proofs.EndotacticPermanence.FamilyPlateau
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Filter Set
open scoped BigOperators Topology

variable {d : ℕ} {R : Type*} [Fintype R]

theorem exists_fixed_scale_margin (source target : R → Fin d → ℕ)
    (B : PositiveRateBox R) (G : GeometricFamily d (sourceComparisons source))
    {h : ℝ}
    (hdrift : ∀ x ∈ Icc (fun _ => h) (fun _ => h⁻¹), ∀ j,
      AffineActive G.slope (fun k => G.offset k h) x j →
      ∀ k : R → ℝ, B.Contains k →
      (∃ e, dot (G.slope j) (reactionVector source target e) ≠ 0) →
        0 < dot (G.slope j) (indexedMassAction source target k x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (fun _ => h) (fun _ => h⁻¹), ∀ j,
      AffineActive G.slope (fun k => G.offset k h) x j →
      ∀ k : R → ℝ, B.Contains k →
      (∃ e, dot (G.slope j) (reactionVector source target e) ≠ 0) →
        δ ≤ dot (G.slope j) (indexedMassAction source target k x) := by
  classical
  let W := {j : Fin G.n // ∃ e, dot (G.slope j) (reactionVector source target e) ≠ 0}
  let C : Set ((Fin d → ℝ) × (R → ℝ)) :=
    Icc (fun _ => h) (fun _ => h⁻¹) ×ˢ Icc B.lower B.upper
  have hC : IsCompact C := (isCompact_reciprocal_box h).prod isCompact_Icc
  have hbound (j : W) : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ C,
      AffineActive G.slope (fun k => G.offset k h) u.1 j.val →
        δ ≤ dot (G.slope j.val) (indexedMassAction source target u.2 u.1) := by
    have hclosed : IsClosed {u : (Fin d → ℝ) × (R → ℝ) |
        AffineActive G.slope (fun k => G.offset k h) u.1 j.val} := by
      simp only [AffineActive, ofPred_forall]
      apply isClosed_iInter
      intro k
      exact isClosed_le (by unfold dot; fun_prop) (by unfold dot; fun_prop)
    have hcompact := hC.inter_right hclosed
    have hcontinuous : Continuous (fun u : (Fin d → ℝ) × (R → ℝ) =>
        dot (G.slope j.val) (indexedMassAction source target u.2 u.1)) := by
      unfold dot indexedMassAction monomial
      fun_prop
    obtain ⟨δ, hδ, hlower⟩ := hcompact.exists_forall_le' hcontinuous.continuousOn (by
      intro u hu
      exact hdrift u.1 hu.1.1 j.val hu.2 u.2
        (fun e => ⟨hu.1.2.1 e, hu.1.2.2 e⟩) j.property)
    exact ⟨δ, hδ, fun u hu ha => hlower u ⟨hu, ha⟩⟩
  choose margin hmargin hmargin_bound using hbound
  obtain ⟨δ, hδ, _, hδbound⟩ := finite_positive_lower_bound Finset.univ margin
    (fun j _ => hmargin j)
  refine ⟨δ, hδ, ?_⟩
  intro x hx j ha k hk hn
  let w : W := ⟨j, hn⟩
  exact (hδbound w (Finset.mem_univ w)).trans
    (hmargin_bound w (x, k) ⟨hx, ⟨fun e => (hk e).1, fun e => (hk e).2⟩⟩ ha)

/-- Endotacticity supplies compact positive plateaux and a common drift margin
at every sufficiently small scale, for the entire positive rate box. -/
theorem exists_endotactic_barriers (source target : R → Fin d → ℕ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (G : GeometricFamily d (sourceComparisons source)) (c : Fin d → ℝ)
    (hc : PositiveState c) :
    ∃ η : ℝ, 0 < η ∧ η ≤ G.scale_bound ∧ η ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < η →
        ∃ j0 : Fin G.n, ∃ K : Set (Fin d → ℝ), ∃ δ : ℝ,
          G.slope j0 = 0 ∧ IsCompact K ∧ Convex ℝ K ∧ c ∈ K ∧
          K ⊆ interior (Icc (fun _ => Real.sqrt h) (fun _ => (Real.sqrt h)⁻¹)) ∧
          (∀ x, x ∈ K ↔ AffineActive G.slope (fun k => G.offset k h) x j0) ∧
          0 < δ ∧
          (∀ x ∈ positiveClass source target c,
            x ∈ Icc (fun _ => h) (fun _ => h⁻¹) → x ∉ K →
            ∀ j, AffineActive G.slope (fun k => G.offset k h) x j →
            ∀ k : R → ℝ, B.Contains k →
              δ ≤ dot (G.slope j) (indexedMassAction source target k x)) := by
  obtain ⟨η0, hη0, hηscale, hηone, hdrift⟩ := exists_active_drift_scale source target endo B G
  have hev : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i : Fin d,
      |Real.log (c i) / Real.log h| < G.gap := by
    apply Filter.eventually_all.mpr
    intro i
    have hlim : Tendsto (fun h : ℝ => |Real.log (c i) / Real.log h|)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using (tendsto_log_coordinate_div_log (c i)).abs
    exact hlim.eventually_lt_const G.gap_pos
  obtain ⟨ρ, hρ, hρprop⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min η0 ρ, lt_min hη0 hρ, (min_le_left _ _).trans hηscale,
    (min_le_left _ _).trans hηone, ?_⟩
  intro h hh hsmall
  have hhη : h < η0 := hsmall.trans_le (min_le_left _ _)
  have hhρ : h < ρ := hsmall.trans_le (min_le_right _ _)
  have hh1 : h < 1 := hhη.trans_le hηone
  have hs : h < G.scale_bound := hhη.trans_le hηscale
  have hp0 := hρprop (show h ∈ Metric.ball 0 ρ ∩ Ioi 0 from
    ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh] using hhρ, hh⟩)
  obtain ⟨j0, K, hz, hKcompact, hKconvex, hcK, hKinside, hKactive, hneutral⟩ :=
    G.exists_plateau source target c hc hh hh1 hs hp0
  have hpositive : ∀ x ∈ Icc (fun _ : Fin d => h) (fun _ => h⁻¹), ∀ j,
      AffineActive G.slope (fun k => G.offset k h) x j →
      ∀ k : R → ℝ, B.Contains k →
      (∃ e, dot (G.slope j) (reactionVector source target e) ≠ 0) →
        0 < dot (G.slope j) (indexedMassAction source target k x) := by
    intro x hx j ha k hk hn
    obtain ⟨_, hp, hrec⟩ := reciprocal_box_log_coordinates hh hh1 hx
    let p : Fin d → ℝ := fun i => Real.log (x i) / Real.log h
    have hpoint : (fun i => h ^ p i) = x := funext hrec
    have hd := hdrift h hh hhη p hp j (by rwa [hpoint]) k hk hn
    rwa [hpoint] at hd
  obtain ⟨δ, hδ, hmargin⟩ := exists_fixed_scale_margin source target B G hpositive
  refine ⟨j0, K, δ, hz, hKcompact, hKconvex, hcK,
    G.plateau_inner_box source hh hh1 hs hz hKinside
      (fun x hx => (hKactive x).mp hx), hKactive, hδ, ?_⟩
  intro x hx hxbox hxnot j ha k hk
  exact hmargin x hxbox j ha k hk (hneutral x hx hxnot j ha)

end EndotacticPermanence
