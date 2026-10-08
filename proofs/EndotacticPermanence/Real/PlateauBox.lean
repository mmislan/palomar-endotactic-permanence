module
public import proofs.EndotacticPermanence.Real.EndotacticBarrier
public import proofs.EndotacticPermanence.AffineObservable
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set

theorem sqrt_box_subset_box {d : ℕ} {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    interior (Icc (fun _ : Fin d => Real.sqrt h) (fun _ => (Real.sqrt h)⁻¹)) ⊆
      interior (Icc (fun _ => h) (fun _ => h⁻¹)) := by
  have hspos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hhs : h ≤ Real.sqrt h := by
    have hs := Real.sq_sqrt hh.le
    nlinarith [Real.sqrt_nonneg h]
  have hinv : (Real.sqrt h)⁻¹ ≤ h⁻¹ := inv_anti₀ hh hhs
  intro x hx
  rw [mem_interior_coordinate_box_iff] at hx ⊢
  exact fun i => ⟨hhs.trans_lt (hx i).1, (hx i).2.trans_le hinv⟩

variable {d : ℕ} {R : Type*} [Fintype R]

theorem small_exponents_mem_plateau (source : R → Fin d → ℝ)
    (G : GeometricFamily d (sourceComparisons source))
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1) (hs : h < G.scale_bound)
    {j0 : Fin G.n} (hz : G.slope j0 = 0) {K : Set (Fin d → ℝ)}
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0)
    (hKne : K.Nonempty) {x : Fin d → ℝ} (hx : PositiveState x)
    (hp : ∀ i, |Real.log (x i) / Real.log h| < G.gap) : x ∈ K := by
  let : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
  obtain ⟨j, hj⟩ := exists_affineActive G.slope (fun k => G.offset k h) x
  have hzj : G.slope j = 0 := by
    apply EndotacticPermanence.RealComplex.GeometricFamily.active_zero_at_inner_exponents source G hh hs hp
    have hxpoint : (fun i => h ^ (Real.log (x i) / Real.log h)) = x :=
      funext (fun i => rpow_log_coordinate hh hh1 (hx i))
    rwa [hxpoint]
  obtain ⟨c, hc⟩ := hKne
  have hcactive := (hK c).mp hc
  apply (hK x).mpr
  intro k
  have h0j : G.offset j0 h ≤ G.offset j h := by
    simpa [hz, hzj, dot] using hcactive j
  have hjk : G.offset j h ≤ dot (G.slope k) x + G.offset k h := by
    simpa [hzj, dot] using hj k
  simpa [hz, dot] using h0j.trans hjk

end
end EndotacticPermanence.RealComplex
