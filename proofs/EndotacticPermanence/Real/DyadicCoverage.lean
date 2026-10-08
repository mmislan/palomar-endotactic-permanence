module
public import proofs.EndotacticPermanence.Real.BarrierFamily
public import proofs.EndotacticPermanence.ScaleIteration

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set Filter
open scoped Topology

variable {d : ℕ} {R : Type*} [Fintype R]

/-- Every positive initial point belongs to a sufficiently small dyadic plateau.
The finite family and target scale are fixed before the point is chosen. -/
theorem dyadic_plateau_covers_positive {source target : R → Fin d → ℝ} {B : PositiveRateBox R}
    {G : GeometricFamily d (sourceComparisons source)} {c : Fin d → ℝ}
    (F : BarrierFamily source target B G c) {p : ℝ} (hp : 0 < p) (hpF : p < F.threshold)
    (x : Fin d → ℝ) (hx : PositiveState x) :
    ∃ n : ℕ, x ∈ (F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
      ((dyadicScale_le hp (hpF.trans_le F.threshold_le_one) n).trans_lt hpF)).plateau := by
  have hp1 := hpF.trans_le F.threshold_le_one
  have hlim : Tendsto (dyadicScale p) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨dyadicScale_tendsto_zero hp hp1, Eventually.of_forall (dyadicScale_pos hp)⟩
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i : Fin d,
      |Real.log (x i) / Real.log (dyadicScale p n)| < G.gap := by
    apply Filter.eventually_all.mpr
    intro i
    have hi : Tendsto (fun n : ℕ => |Real.log (x i) / Real.log (dyadicScale p n)|)
        atTop (𝓝 0) := by
      simpa only [abs_zero, Function.comp_def] using ((tendsto_log_coordinate_div_log (x i)).comp hlim).abs
    exact hi.eventually_lt_const G.gap_pos
  obtain ⟨n, hn⟩ := hev.exists
  let C := F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
    ((dyadicScale_le hp hp1 n).trans_lt hpF)
  refine ⟨n, small_exponents_mem_plateau source G (dyadicScale_pos hp n)
    ((dyadicScale_le hp hp1 n).trans_lt hp1)
    (((dyadicScale_le hp hp1 n).trans_lt hpF).trans_le F.threshold_le_scale)
    C.zero_slope C.active ⟨c, C.center_mem⟩ hx hn⟩

end
end EndotacticPermanence.RealComplex
