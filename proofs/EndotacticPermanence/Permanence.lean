module
public import proofs.EndotacticPermanence.UniformScaleAbsorption
public import proofs.EndotacticPermanence.DyadicCoverage
public import proofs.EndotacticPermanence.CaratheodoryInterface
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

/-- General endotactic permanence for measurable rates in a fixed positive
compact box. The absorbing compact convex set depends only on the network,
rate box and positive stoichiometric class; entry times precede rate histories. -/
theorem endotactic_permanence (source target : R → Fin d → ℕ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (c : Fin d → ℝ) (hc : PositiveState c) :
    ∃ K : Set (Fin d → ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      K ⊆ positiveClass source target c ∧
      (∀ x0 ∈ positiveClass source target c, ∃ T : ℝ, 0 ≤ T ∧
        ∀ k : ℝ → R → ℝ, (∀ e, Measurable (fun t => k t e)) →
          (∀ t : ℝ, 0 ≤ t → B.Contains (k t)) →
          ∃ x : ℝ → (Fin d → ℝ),
            IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x ∧
            (∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c) ∧
            (∀ t : ℝ, T ≤ t → x t ∈ K) ∧
            (∀ y : ℝ → (Fin d → ℝ),
              IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 y →
                EqOn x y (Ici 0))) ∧
      (∀ x0 ∈ K, ∀ k : ℝ → R → ℝ, (∀ e, Measurable (fun t => k t e)) →
        (∀ t : ℝ, 0 ≤ t → B.Contains (k t)) →
        ∀ x : ℝ → (Fin d → ℝ),
          IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x →
          ∀ t : ℝ, 0 ≤ t → x t ∈ K) := by
  classical
  obtain ⟨G⟩ := exists_geometric_family d (sourceComparisons source)
  obtain ⟨F⟩ := exists_barrier_family source target endo B G c hc
  let p := F.threshold / 2
  have hp : 0 < p := by dsimp [p]; exact half_pos F.threshold_pos
  have hpF : p < F.threshold := by dsimp [p]; linarith [F.threshold_pos]
  have hp1 : p < 1 := hpF.trans_le F.threshold_le_one
  let C := fun n => F.atScale (dyadicScale p n) (dyadicScale_pos hp n)
    ((dyadicScale_le hp hp1 n).trans_lt hpF)
  let S := stoichiometricSubspace source target
  let K : Set (Fin d → ℝ) := (C 0).plateau ∩ {x | x - c ∈ S}
  have hclosed : IsClosed {x : Fin d → ℝ | x - c ∈ S} :=
    S.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  have hcompact : IsCompact K := (C 0).compact.inter_right hclosed
  have hcK : c ∈ K := ⟨(C 0).center_mem, by simp [S]⟩
  have hconvex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    refine ⟨(C 0).convex hx.1 hy.1 ha hb hab, ?_⟩
    have hs := S.add_mem (S.smul_mem a hx.2) (S.smul_mem b hy.2)
    have heq : (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
      funext i
      change a * x i + b * y i - c i = a * (x i - c i) + b * (y i - c i)
      nlinarith [congrArg (fun u : ℝ => u * c i) hab]
    change (a • x + b • y) - c ∈ S
    rw [heq]
    exact hs
  have hsubset : K ⊆ positiveClass source target c := by
    intro x hx
    have hb := interior_subset ((C 0).box_interior (dyadicScale_pos hp 0)
      ((dyadicScale_le hp hp1 0).trans_lt hp1) hx.1)
    exact ⟨fun i => (dyadicScale_pos hp 0).trans_le (hb.1 i), hx.2⟩
  have hclass {x0 : Fin d → ℝ} {k : ℝ → R → ℝ} {x : ℝ → (Fin d → ℝ)}
      (hx0 : x0 ∈ positiveClass source target c)
      (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x)
      (hxpos : ∀ t : ℝ, 0 ≤ t → PositiveState (x t)) :
      ∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c := by
    intro t ht
    exact ⟨hxpos t ht, mass_action_curve_in_class source target k hx0.2 hx t ht⟩
  refine ⟨K, ⟨c, hcK⟩, hcompact, hconvex, hsubset, ?_, ?_⟩
  · intro x0 hx0
    obtain ⟨n, hn⟩ := dyadic_plateau_covers_positive F hp hpF x0 hx0.1
    obtain ⟨T, hT, hprop⟩ := uniform_scale_absorption F hp hpF n
    refine ⟨T, hT, ?_⟩
    intro k hk hkbox
    obtain ⟨x, hx, hxpos, hunique⟩ := global_mass_action_existence source target endo B k hk hkbox x0 hx0.1
    have hxclass := hclass hx0 hx hxpos
    have hin : ∀ t : ℝ, 0 ≤ t → x t ∈ (C n).plateau :=
      (C n).invariant (dyadicScale_pos hp n) ((dyadicScale_le hp hp1 n).trans_lt hp1)
        k hk hkbox hn hx0.2 hx
    have hentry := hprop 0 le_rfl k hkbox x0 x hx hxclass hin
    refine ⟨x, hx, hxclass, ?_, hunique⟩
    intro t ht
    exact ⟨hentry t (by simpa only [zero_add] using ht), (hxclass t (hT.trans ht)).2⟩
  · intro x0 hx0 k hk hkbox x hx t ht
    have hin := (C 0).invariant (dyadicScale_pos hp 0)
      ((dyadicScale_le hp hp1 0).trans_lt hp1) k hk hkbox hx0.1 hx0.2 hx
    exact ⟨hin t ht, mass_action_curve_in_class source target k hx0.2 hx t ht⟩

/-- The same literal root in the standard AC/a.e.-ODE formulation,
with uniqueness over all such solutions, without an integral premise. -/
theorem endotactic_permanence_caratheodory (source target : R → Fin d → ℕ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (c : Fin d → ℝ) (hc : PositiveState c) :
    ∃ K : Set (Fin d → ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      K ⊆ positiveClass source target c ∧
      (∀ x0 ∈ positiveClass source target c, ∃ T : ℝ, 0 ≤ T ∧
        ∀ k : ℝ → R → ℝ, (∀ e, Measurable (fun t => k t e)) →
          (∀ t : ℝ, 0 ≤ t → B.Contains (k t)) →
          ∃ x : ℝ → (Fin d → ℝ),
            IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x ∧
            (∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c) ∧
            (∀ t : ℝ, T ≤ t → x t ∈ K) ∧
            (∀ y : ℝ → (Fin d → ℝ),
              IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 y →
                EqOn x y (Ici 0))) ∧
      (∀ x0 ∈ K, ∀ k : ℝ → R → ℝ, (∀ e, Measurable (fun t => k t e)) →
        (∀ t : ℝ, 0 ≤ t → B.Contains (k t)) →
        ∀ x : ℝ → (Fin d → ℝ),
          IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x →
          ∀ t : ℝ, 0 ≤ t → x t ∈ K) := by
  obtain ⟨K, hne, hcomp, hconv, hsub, habs, hinv⟩ := endotactic_permanence source target endo B c hc
  refine ⟨K, hne, hcomp, hconv, hsub, ?_, ?_⟩
  · intro x0 hx0
    obtain ⟨T, hT, hsol⟩ := habs x0 hx0
    refine ⟨T, hT, ?_⟩
    intro k hk hkbox
    obtain ⟨x, hx, hclass, hentry, huniq⟩ := hsol k hk hkbox
    exact ⟨x, forward_curve_iff_ac_ode.mp hx, hclass, hentry,
      fun y hy => huniq y (forward_curve_iff_ac_ode.mpr hy)⟩
  · intro x0 hx0 k hk hkbox x hx
    exact hinv x0 hx0 k hk hkbox x (forward_curve_iff_ac_ode.mpr hx)

end EndotacticPermanence
