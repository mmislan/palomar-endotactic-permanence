module
public import proofs.EndotacticPermanence.GeometricFamily
public import proofs.EndotacticPermanence.MassActionModel
public import Mathlib.Tactic.Choose

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Filter Set
open scoped BigOperators Topology

variable {d : ℕ} {R : Type*} [Fintype R]

def coordinateDirection (i : Fin d) : Fin d → ℝ := fun k => if k = i then 1 else 0

def sourceDifference (source : R → Fin d → ℕ) (j e : R) : Fin d → ℝ :=
  fun i => (source e i : ℝ) - (source j i : ℝ)

noncomputable def sourceComparisons (source : R → Fin d → ℕ) : Finset (Fin d → ℝ) := by
  classical
  exact (Finset.univ.image coordinateDirection) ∪
    ((Finset.univ : Finset (R × R)).image (fun je => sourceDifference source je.1 je.2))

theorem source_difference_mem (source : R → Fin d → ℕ) (j e : R) :
    sourceDifference source j e ∈ sourceComparisons source := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, e)))

omit [Fintype R] in
theorem dot_source_difference (source : R → Fin d → ℕ) (r : Fin d → ℝ) (j e : R) :
    dot r (sourceDifference source j e) =
      dot r (fun i => (source e i : ℝ)) - dot r (fun i => (source j i : ℝ)) := by
  simp [dot, sourceDifference, mul_sub, Finset.sum_sub_distrib]

theorem active_source_ratio (source : R → Fin d → ℕ)
    (G : GeometricFamily d (sourceComparisons source))
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hscale : h < G.scale_bound)
    {p : Fin d → ℝ} (hp : ∀ i, |p i| ≤ 1) {l : Fin G.n}
    (ha : AffineActive G.slope (fun k => G.offset k h) (fun i => h ^ p i) l)
    {j e : R}
    (horder : dot (G.slope l) (fun i => (source j i : ℝ)) <
      dot (G.slope l) (fun i => (source e i : ℝ))) :
    monomial (fun i => h ^ p i) (source e) ≤
      h ^ G.gap * monomial (fun i => h ^ p i) (source j) := by
  have hr : 0 < dot (G.slope l) (sourceDifference source j e) := by
    rw [dot_source_difference]
    exact sub_pos.mpr horder
  have hg := G.active_gap hh hscale hp ha (source_difference_mem source j e) hr.ne'
  have hpg : 0 < dot p (sourceDifference source j e) := hg.1.mpr hr
  have hgap : G.gap ≤ dot p (sourceDifference source j e) := by
    simpa only [abs_of_pos hpg] using hg.2.le
  exact monomial_le_rpow_mul_of_gap hh hh1 p (source j) (source e) hgap

/-- One threshold works for all fixed slopes and every rate vector in the box.
The reaction projection lengths are explicitly included in the threshold. -/
theorem exists_active_drift_scale (source target : R → Fin d → ℕ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (G : GeometricFamily d (sourceComparisons source)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ G.scale_bound ∧ η ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < η → ∀ p : Fin d → ℝ,
        (∀ i, |p i| ≤ 1) → ∀ l : Fin G.n,
          AffineActive G.slope (fun k => G.offset k h) (fun i => h ^ p i) l →
          ∀ k : R → ℝ, B.Contains k →
            (∃ e, dot (G.slope l) (reactionVector source target e) ≠ 0) →
              0 < dot (G.slope l) (indexedMassAction source target k (fun i => h ^ p i)) := by
  classical
  let a (l : Fin G.n) (e : R) := dot (G.slope l) (reactionVector source target e)
  let level (l : Fin G.n) (e : R) := dot (G.slope l) (fun i => (source e i : ℝ))
  let W := {l : Fin G.n // ∃ e, a l e ≠ 0}
  have hw : ∀ l : W, ∃ j : R, 0 < a l.val j ∧
      ∀ e, a l.val e < 0 → level l.val j < level l.val e := by
    intro l
    rcases witness_or_neutral (a l.val) (level l.val) (endo (G.slope l.val)) with hn | hj
    · obtain ⟨e, he⟩ := l.property
      exact False.elim (he (hn e))
    · exact hj
  choose witness hwpos hworder using hw
  let beta (l : W) : ℝ := ∑ e : R, if a l.val e < 0 then B.upper e * |a l.val e| else 0
  have hev : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ l : W,
      h ^ G.gap * beta l ≤ B.lower (witness l) * a l.val (witness l) / 2 := by
    apply Filter.eventually_all.mpr
    intro l
    have hpow : Tendsto (fun h : ℝ => h ^ G.gap) (𝓝[>] 0) (𝓝 0) :=
      tendsto_positive_rpow_nhdsGT_zero G.gap_pos
    have hlim := hpow.mul_const (beta l)
    have hpos : 0 < B.lower (witness l) * a l.val (witness l) / 2 :=
      half_pos (mul_pos (B.lower_pos _) (hwpos l))
    have hlt := hlim.eventually_lt_const (by simpa only [zero_mul] using hpos)
    exact hlt.mono (fun h hh => hh.le)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let η := min 1 (min G.scale_bound δ)
  have hη : 0 < η := lt_min zero_lt_one (lt_min G.scale_pos hδ)
  refine ⟨η, hη, (min_le_right _ _).trans (min_le_left _ _), min_le_left _ _, ?_⟩
  intro h hh hηh p hp l ha k hk hn
  have hs : h < G.scale_bound := hηh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h1 : h ≤ 1 := hηh.le.trans (min_le_left _ _)
  have hd : h < δ := hηh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbudget := hδprop (show h ∈ Metric.ball 0 δ ∩ Ioi 0 from
    ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh] using hd, hh⟩)
  let w : W := ⟨l, hn⟩
  rw [indexed_mass_action_dot]
  apply rate_box_half_margin (a l) (fun e => monomial (fun i => h ^ p i) (source e))
    B.lower B.upper k (witness w) (h ^ G.gap)
    (fun e => Finset.prod_pos (fun i _ => pow_pos (Real.rpow_pos_of_pos hh _) _))
    B.lower_pos hk (hwpos w)
  · intro e he
    exact active_source_ratio source G hh h1 hs hp ha (hworder w e he)
  · exact hbudget w

end EndotacticPermanence
