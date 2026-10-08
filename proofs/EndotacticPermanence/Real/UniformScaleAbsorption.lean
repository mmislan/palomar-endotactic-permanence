module
public import proofs.EndotacticPermanence.Real.BarrierInvariance
public import proofs.EndotacticPermanence.Real.MassActionDynamics
public import proofs.EndotacticPermanence.ScaleIteration
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

/-- Induction over dyadic scales gives a delay uniform in the rate history,
starting time, and all states in the preceding compact plateau. -/
theorem uniform_scale_absorption {source target : R → Fin d → ℝ} {B : PositiveRateBox R}
    {G : GeometricFamily d (sourceComparisons source)} {c : Fin d → ℝ}
    (F : BarrierFamily source target B G c) {p : ℝ} (hp : 0 < p) (hpF : p < F.threshold) :
    let C := fun n => F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
      ((dyadicScale_le hp (hpF.trans_le F.threshold_le_one) n).trans_lt hpF)
    ∀ n : ℕ, ∃ T : ℝ, 0 ≤ T ∧
      ∀ a : ℝ, 0 ≤ a → ∀ k : ℝ → R → ℝ,
        (∀ t : ℝ, 0 ≤ t → B.Contains (k t)) →
        ∀ x0 : Fin d → ℝ, ∀ x : ℝ → (Fin d → ℝ),
          IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x →
          (∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c) →
          (∀ t : ℝ, a ≤ t → x t ∈ (C n).plateau) →
          ∀ t : ℝ, a + T ≤ t → x t ∈ (C 0).plateau := by
  dsimp only
  let C := fun n => F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
    ((dyadicScale_le hp (hpF.trans_le F.threshold_le_one) n).trans_lt hpF)
  intro n
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro a _ k _ x0 x _ _ hxin t ht
    exact hxin t (by simpa only [add_zero] using ht)
  | succ n ih =>
    obtain ⟨T, hT, hprop⟩ := ih
    obtain ⟨z, hz, hmin⟩ := (C (n + 1)).compact.exists_isMinOn
      ⟨c, (C (n + 1)).center_mem⟩
      (EndotacticPermanence.RealComplex.GeometricFamily.envelope_continuous G
        (dyadicScale p n)).continuousOn
    let A := G.envelope (dyadicScale p n) z
    let L := (G.offset (C n).label (dyadicScale p n) - A) / (C n).margin + 1
    have hcap : A ≤ G.offset (C n).label (dyadicScale p n) := by
      have hmc := hmin (C (n + 1)).center_mem
      have hce := G.envelope_le (dyadicScale p n) c (C n).label
      simp only [(C n).zero_slope, dot, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, zero_add] at hce
      exact hmc.trans hce
    have hL : 0 ≤ L := by
      have hdiv := div_nonneg (sub_nonneg.mpr hcap) (C n).margin_pos.le
      dsimp only [L]
      linarith
    have hbox : (C (n + 1)).plateau ⊆
        Icc (fun _ => dyadicScale p n) (fun _ => (dyadicScale p n)⁻¹) := by
      intro w hw
      have hi := interior_subset ((C (n + 1)).inner hw)
      simpa only [sqrt_dyadicScale_succ hp n] using hi
    refine ⟨L + T, add_nonneg hL hT, ?_⟩
    intro a ha k hkbox x0 x hx hxclass hxin t ht
    have hentry := mass_action_finite_entry source target B G c a ha
      (C n).margin_pos (C n).zero_slope (C n).active (C n).drift k hkbox hx hxclass
      (fun u hu => hbox (hxin u hu)) (hmin (hxin a le_rfl))
    have hin : ∀ u : ℝ, a + L ≤ u → x u ∈ (C n).plateau := by
      intro u hu
      apply hentry.2 u
      dsimp only [L, A] at hu
      linarith
    apply hprop (a + L) (add_nonneg ha hL) k hkbox x0 x hx hxclass hin t
    linarith

end
end EndotacticPermanence.RealComplex
