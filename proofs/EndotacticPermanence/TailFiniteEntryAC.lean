module
public import proofs.EndotacticPermanence.FiniteEntryAC
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace EndotacticPermanence

open Set Filter MeasureTheory

theorem finite_entry_on_tail {g : ℝ → ℝ} {a M A δ : ℝ}
    (hδ : 0 < δ) (hA : A ≤ g a) (hcap : ∀ t, a ≤ t → g t ≤ M)
    (hac : ∀ T : ℝ, a ≤ T → AbsolutelyContinuousOnInterval g a T)
    (hmono : ∀ T : ℝ, a ≤ T → MonotoneOn g (Icc a T))
    (hdr : ∀ T : ℝ, a ≤ T → ∀ᵐ t,
      t ∈ Icc a T → g t < M → δ ≤ deriv g t) :
    a ≤ a + (M - A) / δ + 1 ∧
      ∀ t : ℝ, a + (M - A) / δ + 1 ≤ t → g t = M := by
  let T := a + (M - A) / δ + 1
  have hMA : 0 ≤ M - A := sub_nonneg.mpr (hA.trans (hcap a le_rfl))
  have hT : a ≤ T := by
    have hdiv : 0 ≤ (M - A) / δ := div_nonneg hMA hδ.le
    dsimp [T]
    linarith
  have hreach : g T = M := by
    by_contra hn
    have hlt : g T < M := lt_of_le_of_ne (hcap T hT) hn
    have hall : ∀ t ∈ Icc a T, g t < M := fun t ht =>
      lt_of_le_of_lt (hmono T hT ht ⟨hT, le_rfl⟩ ht.2) hlt
    have hd : ∀ᵐ t, t ∈ Icc a T → δ ≤ deriv g t := by
      filter_upwards [hdr T hT] with t ht htmem
      exact ht htmem (hall t htmem)
    have hi := ac_integrated_drift hT (hac T hT) hd
    have hmul : δ * (T - a) = M - A + δ := by
      dsimp [T]
      field_simp [ne_of_gt hδ]
      ring
    rw [hmul] at hi
    linarith
  refine ⟨hT, ?_⟩
  intro t ht
  apply le_antisymm (hcap t (hT.trans ht))
  rw [← hreach]
  exact hmono t (hT.trans ht) ⟨hT, ht⟩ ⟨hT.trans ht, le_rfl⟩ ht

end EndotacticPermanence
