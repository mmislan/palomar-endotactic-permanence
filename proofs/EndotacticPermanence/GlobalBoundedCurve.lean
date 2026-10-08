module
public import proofs.EndotacticPermanence.BoundedField
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace EndotacticPermanence

open Set MeasureTheory Filter
open scoped Topology

variable {d : ℕ} {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}

/-- Compatible finite-interval Picard solutions construct a global curve.
The field bounds are hypotheses on an extension, not assumptions about a solution. -/
theorem BoundedTimeField.exists_global_curve (F : BoundedTimeField d f) (x0 : Fin d → ℝ) :
    ∃ x : ℝ → (Fin d → ℝ), x 0 = x0 ∧
      (∀ T : ℝ, 0 ≤ T → IsIntegralCurveOn f x0 T x) ∧
      (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval x 0 T) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (f t (x t)) t) := by
  have hex (n : ℕ) := F.exists_integral_curve x0 (show (0 : ℝ) ≤ n by positivity)
  choose z hz using hex
  let idx : ℝ → ℕ := fun t => Nat.ceil t + 1
  have hidx (t : ℝ) : t ≤ (idx t : ℝ) := by
    exact (Nat.le_ceil t).trans (by dsimp [idx]; norm_cast; omega)
  let x : ℝ → (Fin d → ℝ) := fun t => z (idx t) t
  have hagree (T : ℝ) (hT : 0 ≤ T) : EqOn x (z (idx T)) (Icc 0 T) := by
    intro t ht
    have hx := (hz (idx t)).1.mono ht.1 (hidx t)
    have hy := (hz (idx T)).1.mono ht.1 (ht.2.trans (hidx T))
    exact F.integral_curve_unique ht.1 hx hy ⟨ht.1, le_rfl⟩
  have hint (T : ℝ) (hT : 0 ≤ T) : IsIntegralCurveOn f x0 T x := by
    have hzT := (hz (idx T)).1.mono hT (hidx T)
    have heq := hagree T hT
    refine ⟨hzT.1.congr_ae ?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have htT : t ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using uIoc_subset_uIcc ht
      rw [heq htT]
    · intro t ht
      rw [heq ht, hzT.2 t ht]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      change f s (z (idx T) s) = f s (x s)
      rw [heq (uIcc_subset_Icc ⟨le_rfl, hT⟩ ht hs)]
  refine ⟨x, ?_, hint, ?_, ?_⟩
  · exact (hz (idx 0)).2.1
  · intro T hT
    have hlip : LipschitzOnWith F.bound x (uIcc 0 T) := by
      simpa only [uIcc_of_le hT] using F.integral_curve_lipschitz hT (hint T hT)
    exact hlip.absolutelyContinuousOnInterval
  · intro T hT
    have hode := (hz (idx T)).2.2.2
    filter_upwards [hode] with t ht htT
    have hi : t ∈ Ioo 0 (idx T : ℝ) := ⟨htT.1, htT.2.trans_le (hidx T)⟩
    have heq : x =ᶠ[𝓝 t] z (idx T) := by
      filter_upwards [Ioo_mem_nhds htT.1 htT.2] with u hu
      exact hagree T hT ⟨hu.1.le, hu.2.le⟩
    have hh := (ht hi).congr_of_eventuallyEq heq
    rwa [← heq.eq_of_nhds] at hh

end EndotacticPermanence
