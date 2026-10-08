module
public import proofs.EndotacticPermanence.DyadicCoverage

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set Filter
open scoped Topology

variable {d : ℕ} {R : Type*} [Fintype R]

/-- A common starting plateau for a compact positive set. No inference from
pointwise entry times or continuity of entry times is used. -/
theorem dyadic_plateau_covers_compact {source target : R → Fin d → ℕ}
    {B : PositiveRateBox R} {G : GeometricFamily d (sourceComparisons source)}
    {c : Fin d → ℝ} (F : BarrierFamily source target B G c)
    {p : ℝ} (hp : 0 < p) (hpF : p < F.threshold)
    (Q : Set (Fin d → ℝ)) (hQ : IsCompact Q)
    (hpos : ∀ x ∈ Q, PositiveState x) :
    ∃ n : ℕ, ∀ x ∈ Q, x ∈ (F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
      ((dyadicScale_le hp (hpF.trans_le F.threshold_le_one) n).trans_lt hpF)).plateau := by
  have hlog : ContinuousOn (fun x : Fin d → ℝ => fun i => Real.log (x i)) Q := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i).continuousOn.log (fun x hx => ne_of_gt (hpos x hx i))
  obtain ⟨A, hA⟩ := hQ.exists_bound_of_continuousOn hlog
  let L : ℝ := max A 0
  have hL : 0 ≤ L := le_max_right _ _
  have hbound : ∀ x ∈ Q, ∀ i : Fin d, |Real.log (x i)| ≤ L := by
    intro x hx i
    have hi : |Real.log (x i)| ≤ ‖fun i => Real.log (x i)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => Real.log (x i)) i
    exact hi.trans ((hA x hx).trans (le_max_left A 0))
  have hp1 := hpF.trans_le F.threshold_le_one
  have hlim : Tendsto (dyadicScale p) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨dyadicScale_tendsto_zero hp hp1, Eventually.of_forall (dyadicScale_pos hp)⟩
  have hratio : Tendsto (fun n : ℕ => |L / Real.log (dyadicScale p n)|) atTop (𝓝 0) := by
    simpa only [Real.log_exp, abs_zero, Function.comp_def] using
      ((tendsto_log_coordinate_div_log (Real.exp L)).comp hlim).abs
  obtain ⟨n, hn⟩ := (hratio.eventually_lt_const G.gap_pos).exists
  refine ⟨n, ?_⟩
  intro x hx
  let C := F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
    ((dyadicScale_le hp hp1 n).trans_lt hpF)
  apply small_exponents_mem_plateau source G (dyadicScale_pos hp n)
    ((dyadicScale_le hp hp1 n).trans_lt hp1)
    (((dyadicScale_le hp hp1 n).trans_lt hpF).trans_le F.threshold_le_scale)
    C.zero_slope C.active ⟨c, C.center_mem⟩ (hpos x hx)
  intro i
  apply lt_of_le_of_lt _ hn
  rw [abs_div, abs_div, abs_of_nonneg hL]
  exact div_le_div_of_nonneg_right (hbound x hx i) (abs_nonneg _)

end EndotacticPermanence
