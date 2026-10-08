module
public import proofs.EndotacticPermanence.Real.NetworkDrift
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set
open scoped BigOperators

variable {d : ℕ} {R : Type*} [Fintype R]

theorem coordinate_comparison_mem (source : R → Fin d → ℝ) (i : Fin d) :
    coordinateDirection i ∈ sourceComparisons source := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

@[simp] theorem dot_coordinate_comparison (r : Fin d → ℝ) (i : Fin d) :
    dot r (coordinateDirection i) = r i := by
  classical
  simp [coordinateDirection, dot, mul_ite]

omit [Fintype R] in
theorem neutral_dot_class (source target : R → Fin d → ℝ) (r c x : Fin d → ℝ)
    (hn : ∀ e, dot r (reactionVector source target e) = 0)
    (hx : x - c ∈ stoichiometricSubspace source target) : dot r x = dot r c := by
  have hs : dot r (x - c) = 0 := by
    have hall : ∀ v ∈ stoichiometricSubspace source target, dot r v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨e, rfl⟩ := hv
        exact hn e
      | zero => simp [dot]
      | add v w hv hw ihv ihw => rw [dot_add_right, ihv, ihw, zero_add]
      | smul t v hv ih => rw [dot_smul_right, ih, mul_zero]
    exact hall (x - c) hx
  have he : dot r (x - c) = dot r x - dot r c := by
    simp [dot, mul_sub, Finset.sum_sub_distrib]
  rw [he] at hs
  exact sub_eq_zero.mp hs

namespace GeometricFamily

theorem active_zero_at_inner_exponents (source : R → Fin d → ℝ)
    (G : GeometricFamily d (sourceComparisons source))
    {h : ℝ} (hh : 0 < h) (hs : h < G.scale_bound)
    {p : Fin d → ℝ} (hp : ∀ i, |p i| < G.gap) {j : Fin G.n}
    (ha : AffineActive G.slope (fun k => G.offset k h) (fun i => h ^ p i) j) :
    G.slope j = 0 := by
  funext i
  by_contra hn
  have hi : G.slope j i ≠ 0 := hn
  have hg := G.active_gap hh hs (fun i => (hp i).le.trans G.gap_le_one) ha
    (coordinate_comparison_mem source i) (by simpa using hi)
  have hgap : G.gap < |p i| := by simpa using hg.2
  exact (not_lt_of_ge (hp i).le) hgap

theorem exists_plateau (source target : R → Fin d → ℝ)
    (G : GeometricFamily d (sourceComparisons source)) (c : Fin d → ℝ)
    (hc : PositiveState c) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hs : h < G.scale_bound)
    (hp0 : ∀ i, |Real.log (c i) / Real.log h| < G.gap) :
    ∃ j0 : Fin G.n, ∃ K : Set (Fin d → ℝ),
      G.slope j0 = 0 ∧ IsCompact K ∧ Convex ℝ K ∧ c ∈ K ∧
      K ⊆ interior (Icc (fun _ => h) (fun _ => h⁻¹)) ∧
      (∀ x, x ∈ K ↔ AffineActive G.slope (fun k => G.offset k h) x j0) ∧
      (∀ x ∈ positiveClass source target c, x ∉ K → ∀ j,
        AffineActive G.slope (fun k => G.offset k h) x j →
          ∃ e, dot (G.slope j) (reactionVector source target e) ≠ 0) := by
  let : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  let p0 : Fin d → ℝ := fun i => Real.log (c i) / Real.log h
  have hcpoint : (fun i => h ^ p0 i) = c :=
    funext (fun i => rpow_log_coordinate hh hh1 (hc i))
  obtain ⟨j0, hj0⟩ := exists_affineActive G.slope (fun k => G.offset k h) c
  have hz : G.slope j0 = 0 := by
    apply EndotacticPermanence.RealComplex.GeometricFamily.active_zero_at_inner_exponents source G hh hs hp0
    rwa [hcpoint]
  have hcinside : c ∈ interior (Icc (fun _ => h) (fun _ => h⁻¹)) :=
    (mem_interior_reciprocal_box_iff hh hh1 hc).mpr
      (fun i => (hp0 i).trans_le G.gap_le_one)
  have hboundary : ∀ x ∈ frontier (Icc (fun _ : Fin d => h) (fun _ => h⁻¹)),
      ∀ j, AffineActive G.slope (fun k => G.offset k h) x j → G.slope j ≠ 0 := by
    intro x hx j ha hjz
    have hxbox := isClosed_Icc.frontier_subset hx
    obtain ⟨hxp, hp, hrec⟩ := reciprocal_box_log_coordinates hh hh1 hxbox
    obtain ⟨i, hi⟩ := reciprocal_box_frontier_coordinate hh hh1 hx
    let p : Fin d → ℝ := fun i => Real.log (x i) / Real.log h
    have hpoint : (fun i => h ^ p i) = x := funext hrec
    have happ := G.approximates h hh hs p hp j (by rwa [hpoint]) i
    simp only [hjz, Pi.zero_apply, sub_zero] at happ
    have htol := G.tolerance_half 0
    change |Real.log (x i) / Real.log h| < G.tolerance 0 at happ
    linarith
  obtain ⟨K, hKcompact, hKconvex, _, hcK, hKinside, hKcut⟩ :=
    compact_polyhedron_of_zero_active_slope G.slope (fun k => G.offset k h) j0
      (Icc (fun _ => h) (fun _ => h⁻¹)) c (isCompact_reciprocal_box h)
      hcinside hz hj0 hboundary
  have hKactive : ∀ x, x ∈ K ↔ AffineActive G.slope (fun k => G.offset k h) x j0 := by
    intro x
    rw [hKcut]
    simp only [AffineActive, hz, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  refine ⟨j0, K, hz, hKcompact, hKconvex, hcK, hKinside, hKactive, ?_⟩
  intro x hx hxnot j ha
  by_contra hn
  push Not at hn
  have hdot := neutral_dot_class source target (G.slope j) c x hn hx.2
  have hupper := ha j0
  have hlower := hj0 j
  simp only [hz, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at hupper hlower
  have hvalue : dot (G.slope j) x + G.offset j h = G.offset j0 h := by
    change dot (G.slope j) x + G.offset j h ≤ G.offset j0 h at hupper
    change G.offset j0 h ≤ dot (G.slope j) c + G.offset j h at hlower
    rw [hdot] at hupper ⊢
    exact le_antisymm hupper hlower
  apply hxnot
  rw [hKcut]
  intro k
  rw [← hvalue]
  exact ha k

/-- Activity of the zero branch puts the entire plateau inside the next box. -/
theorem plateau_inner_box (source : R → Fin d → ℝ)
    (G : GeometricFamily d (sourceComparisons source))
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1) (hs : h < G.scale_bound)
    {j0 : Fin G.n} (hz : G.slope j0 = 0) {K : Set (Fin d → ℝ)}
    (hinside : K ⊆ interior (Icc (fun _ => h) (fun _ => h⁻¹)))
    (hactive : ∀ x ∈ K, AffineActive G.slope (fun k => G.offset k h) x j0) :
    K ⊆ interior (Icc (fun _ => Real.sqrt h) (fun _ => (Real.sqrt h)⁻¹)) := by
  intro x hx
  have hxbox := interior_subset (hinside hx)
  obtain ⟨hxp, hp, hrec⟩ := reciprocal_box_log_coordinates hh hh1 hxbox
  let p : Fin d → ℝ := fun i => Real.log (x i) / Real.log h
  have hpoint : (fun i => h ^ p i) = x := funext hrec
  have hap := G.approximates h hh hs p hp j0 (by rw [hpoint]; exact hactive x hx)
  rw [mem_interior_coordinate_box_iff]
  intro i
  have hi := hap i
  simp only [hz, Pi.zero_apply, sub_zero] at hi
  have hhalf : |p i| < 1 / 2 := hi.trans_le (G.tolerance_half 0)
  obtain ⟨hl, hu⟩ := abs_lt.mp hhalf
  constructor
  · have he := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hu
    simpa only [Real.sqrt_eq_rpow, p, hrec i] using he
  · have he := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hl
    rw [Real.rpow_neg hh.le] at he
    simpa only [Real.sqrt_eq_rpow, p, hrec i] using he

end GeometricFamily
end
end EndotacticPermanence.RealComplex
