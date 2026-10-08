module
public import proofs.EndotacticPermanence.Real.PlateauBox

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set

variable {d : ℕ} {R : Type*} [Fintype R]

structure BarrierAt (source target : R → Fin d → ℝ) (B : PositiveRateBox R)
    (G : GeometricFamily d (sourceComparisons source)) (c : Fin d → ℝ) (h : ℝ) where
  label : Fin G.n
  plateau : Set (Fin d → ℝ)
  margin : ℝ
  zero_slope : G.slope label = 0
  compact : IsCompact plateau
  convex : Convex ℝ plateau
  center_mem : c ∈ plateau
  inner : plateau ⊆ interior (Icc (fun _ => Real.sqrt h) (fun _ => (Real.sqrt h)⁻¹))
  active : ∀ x, x ∈ plateau ↔ AffineActive G.slope (fun j => G.offset j h) x label
  margin_pos : 0 < margin
  drift : ∀ x ∈ positiveClass source target c,
    x ∈ Icc (fun _ => h) (fun _ => h⁻¹) → x ∉ plateau →
      ∀ j, AffineActive G.slope (fun k => G.offset k h) x j →
        ∀ k : R → ℝ, B.Contains k →
          margin ≤ dot (G.slope j) (indexedMassAction source target k x)

structure BarrierFamily (source target : R → Fin d → ℝ) (B : PositiveRateBox R)
    (G : GeometricFamily d (sourceComparisons source)) (c : Fin d → ℝ) where
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_le_scale : threshold ≤ G.scale_bound
  threshold_le_one : threshold ≤ 1
  atScale : ∀ h : ℝ, 0 < h → h < threshold → BarrierAt source target B G c h

theorem exists_barrier_family (source target : R → Fin d → ℝ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (G : GeometricFamily d (sourceComparisons source)) (c : Fin d → ℝ)
    (hc : PositiveState c) : Nonempty (BarrierFamily source target B G c) := by
  classical
  obtain ⟨η, hη, hηs, hη1, hb⟩ := exists_endotactic_barriers source target endo B G c hc
  have hex (h : ℝ) (hh : 0 < h) (hs : h < η) : Nonempty (BarrierAt source target B G c h) := by
    obtain ⟨j, K, δ, hz, hcomp, hconv, hcK, hi, ha, hδ, hd⟩ := hb h hh hs
    exact ⟨⟨j, K, δ, hz, hcomp, hconv, hcK, hi, ha, hδ, hd⟩⟩
  exact ⟨⟨η, hη, hηs, hη1, fun h hh hs => Classical.choice (hex h hh hs)⟩⟩

theorem BarrierAt.box_interior {source target : R → Fin d → ℝ} {B : PositiveRateBox R}
    {G : GeometricFamily d (sourceComparisons source)} {c : Fin d → ℝ} {h : ℝ}
    (C : BarrierAt source target B G c h) (hh : 0 < h) (hh1 : h < 1) :
    C.plateau ⊆ interior (Icc (fun _ => h) (fun _ => h⁻¹)) :=
  C.inner.trans (sqrt_box_subset_box hh hh1)

theorem GeometricFamily.envelope_continuous {D : Finset (Fin d → ℝ)}
    (G : GeometricFamily d D) (h : ℝ) : Continuous (G.envelope h) := by
  classical
  let : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
  have hf (j : Fin G.n) : Continuous (fun x : Fin d → ℝ => dot (G.slope j) x + G.offset j h) := by
    simpa only [dotCLM_apply] using (dotCLM (G.slope j)).continuous.add_const (G.offset j h)
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun j _ => hf j)

end
end EndotacticPermanence.RealComplex
