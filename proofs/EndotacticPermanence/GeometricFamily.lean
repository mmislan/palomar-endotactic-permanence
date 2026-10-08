module
public import proofs.EndotacticPermanence.AffineGeometry
public import proofs.EndotacticPermanence.Imported.SignTolerance
public import proofs.EndotacticPermanence.Imported.MonomialOrder
public import proofs.EndotacticPermanence.Imported.PlateauCertificate
public import proofs.EndotacticPermanence.Imported.PolyhedronGeometry
public import proofs.EndotacticPermanence.Imported.ReciprocalBox
public import Mathlib.Tactic.Choose

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326
open scoped BigOperators

/-- Fixed finite slopes, all-active approximation, and a uniform nonzero gap.
The comparison set may include comparisons across disconnected components. -/
structure GeometricFamily (d : ℕ) (D : Finset (Fin d → ℝ)) where
  n : ℕ
  n_pos : 0 < n
  slope : Fin n → Fin d → ℝ
  offset : Fin n → ℝ → ℝ
  slope_bound : ∀ j i, |slope j i| ≤ 1
  tolerance : (Fin d → ℝ) → ℝ
  tolerance_pos : ∀ r, 0 < tolerance r
  tolerance_half : ∀ r, tolerance r ≤ 1 / 2
  tolerance_control : ∀ r p, (∀ i, |p i - r i| < tolerance r) →
    ∀ v ∈ D, dot r v ≠ 0 →
      (0 < dot p v ↔ 0 < dot r v) ∧
      (dot p v < 0 ↔ dot r v < 0) ∧ |dot r v| / 2 < |dot p v|
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_bound : ∀ j v, v ∈ D → dot (slope j) v ≠ 0 → gap ≤ |dot (slope j) v| / 2
  scale_bound : ℝ
  scale_pos : 0 < scale_bound
  approximates : ∀ h : ℝ, 0 < h → h < scale_bound → ∀ p : Fin d → ℝ,
    (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
      AffineActive slope (fun k => offset k h) (fun i => h ^ p i) j →
      ∀ i, |p i - slope j i| < tolerance (slope j)

theorem exists_geometric_family (d : ℕ) (D : Finset (Fin d → ℝ)) :
    Nonempty (GeometricFamily d D) := by
  classical
  obtain ⟨E, hE, hEc⟩ := exists_sign_tolerance_function D
  obtain ⟨C, h0, hh0, hu⟩ := affine_geometry d E (fun r => (hE r).1)
  let ι := {L : Affine.Label d // L ∈ C.labels}
  let : Nonempty ι := ⟨⟨C.nonempty.choose, C.nonempty.choose_spec⟩⟩
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let r : Fin (Fintype.card ι) → Fin d → ℝ := fun j => (e.symm j).val.slope
  let b : Fin (Fintype.card ι) → ℝ → ℝ := fun j => (e.symm j).val.offset
  obtain ⟨H, hH, hH1, hHg⟩ := exists_uniform_dot_gap (Finset.univ.image r) D
  refine ⟨{
    n := Fintype.card ι
    n_pos := Fintype.card_pos
    slope := r
    offset := b
    slope_bound := ?_
    tolerance := E
    tolerance_pos := fun r => (hE r).1
    tolerance_half := fun r => (hE r).2
    tolerance_control := hEc
    gap := H
    gap_pos := hH
    gap_le_one := hH1
    gap_bound := ?_
    scale_bound := h0
    scale_pos := hh0
    approximates := ?_ }⟩
  · intro j i
    exact abs_le.mpr (C.slopes (e.symm j).val (e.symm j).property i)
  · intro j v hv hn
    exact hHg (r j) (Finset.mem_image_of_mem r (Finset.mem_univ j)) v hv hn
  · intro h hh hhsmall p hp j ha i
    have hc : Affine.Cube (-1) 1 p := fun k => abs_le.mp (hp k)
    have hact : Affine.Active C.labels (e.symm j).val h (Affine.powerPoint h p) := by
      refine ⟨(e.symm j).property, ?_⟩
      intro J hJ
      have h := ha (e ⟨J, hJ⟩)
      simpa [r, b, Affine.Label.value, dot, Affine.powerPoint] using h
    have hn := hu h hh hhsmall p hc (e.symm j).val (e.symm j).property hact
    have hi := (pi_norm_lt_iff (hE (e.symm j).val.slope).1).mp hn i
    simpa only [r, Pi.sub_apply, Real.norm_eq_abs] using hi

namespace GeometricFamily

theorem active_gap {d : ℕ} {D : Finset (Fin d → ℝ)} (G : GeometricFamily d D)
    {h : ℝ} (hh : 0 < h) (hs : h < G.scale_bound) {p : Fin d → ℝ}
    (hp : ∀ i, |p i| ≤ 1) {j : Fin G.n}
    (ha : AffineActive G.slope (fun k => G.offset k h) (fun i => h ^ p i) j)
    {v : Fin d → ℝ} (hv : v ∈ D) (hne : dot (G.slope j) v ≠ 0) :
    (0 < dot p v ↔ 0 < dot (G.slope j) v) ∧ G.gap < |dot p v| := by
  have ht := G.tolerance_control (G.slope j) p (G.approximates h hh hs p hp j ha) v hv hne
  exact ⟨ht.1, (G.gap_bound j v hv hne).trans_lt ht.2.2⟩

end GeometricFamily
end EndotacticPermanence
