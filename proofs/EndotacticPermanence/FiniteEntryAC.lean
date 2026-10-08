module
public import proofs.EndotacticPermanence.CappedMinimumAC
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace EndotacticPermanence

open Set Filter MeasureTheory

/-- An explicit schedule-independent time follows from a common initial
lower bound and positive drift until the ceiling is reached. -/
theorem finite_entry_from_ac_drift {g : ℝ → ℝ} {M A δ : ℝ}
    (hδ : 0 < δ) (hA : A ≤ g 0) (hcap : ∀ t, 0 ≤ t → g t ≤ M)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T)
    (hmono : ∀ T : ℝ, 0 ≤ T → MonotoneOn g (Icc 0 T))
    (hdr : ∀ T : ℝ, 0 ≤ T → ∀ᵐ t,
      t ∈ Icc 0 T → g t < M → δ ≤ deriv g t) :
    0 ≤ (M - A) / δ + 1 ∧
      ∀ t : ℝ, (M - A) / δ + 1 ≤ t → g t = M := by
  let T := (M - A) / δ + 1
  have hMA : 0 ≤ M - A := sub_nonneg.mpr (hA.trans (hcap 0 le_rfl))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hreach : g T = M := by
    by_contra hn
    have hlt : g T < M := lt_of_le_of_ne (hcap T hT) hn
    have hall : ∀ t ∈ Icc 0 T, g t < M := fun t ht =>
      lt_of_le_of_lt (hmono T hT ht ⟨hT, le_rfl⟩ ht.2) hlt
    have hd : ∀ᵐ t, t ∈ Icc 0 T → δ ≤ deriv g t := by
      filter_upwards [hdr T hT] with t ht htmem
      exact ht htmem (hall t htmem)
    have hi := ac_integrated_drift hT (hac T hT) hd
    have hmul : δ * T = M - A + δ := by
      dsimp [T]
      field_simp [ne_of_gt hδ]
    have hdiff : g T - g 0 < M - A := by linarith
    rw [sub_zero, hmul] at hi
    linarith
  refine ⟨hT, ?_⟩
  intro t ht
  apply le_antisymm (hcap t (hT.trans ht))
  rw [← hreach]
  exact hmono t (hT.trans ht) ⟨hT, ht⟩ ⟨hT.trans ht, le_rfl⟩ ht

end EndotacticPermanence
