module
public import proofs.EndotacticPermanence.Real.MassActionModel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace EndotacticPermanence.RealComplex

open OAI.Problem326 Set MeasureTheory Metric
open scoped BigOperators NNReal Topology

variable {d : ℕ} {R : Type*} [Fintype R]

/-- Joint regularity is asserted only where every state coordinate is positive. -/
theorem contDiffAt_indexed_mass_action (source target : R → Fin d → ℝ)
    (kx : (R → ℝ) × (Fin d → ℝ)) (hx : PositiveState kx.2) :
    ContDiffAt ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) =>
      indexedMassAction source target u.1 u.2) kx := by
  have heval (i : Fin d) :
      ContDiffAt ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) => u.2 i) kx := by
    fun_prop
  have hlog (i : Fin d) :
      ContDiffAt ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) => Real.log (u.2 i)) kx :=
    (heval i).log (hx i).ne'
  have hmono (e : R) :
      ContDiffAt ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) => monomial u.2 (source e)) kx := by
    unfold monomial
    fun_prop
  unfold indexedMassAction
  fun_prop

theorem contDiffOn_indexed_mass_action (source target : R → Fin d → ℝ) :
    ContDiffOn ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) =>
      indexedMassAction source target u.1 u.2) {u | PositiveState u.2} := by
  intro u hu
  exact (contDiffAt_indexed_mass_action source target u hu).contDiffWithinAt

omit [Fintype R] in
/-- A compact subset of the positive orthant admits a strictly positive box
enclosure. Empty compact sets and zero species are included. -/
theorem compact_positive_box {C : Set (Fin d → ℝ)}
    (hC : IsCompact C) (hpos : ∀ x ∈ C, PositiveState x) :
    ∃ a b : Fin d → ℝ, (∀ i, 0 < a i) ∧ a ≤ b ∧ C ⊆ Icc a b := by
  have hlow (i : Fin d) : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ C, a ≤ x i :=
    hC.exists_forall_le' (continuous_apply i).continuousOn (fun x hx => hpos x hx i)
  choose a ha hlower using hlow
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn continuous_id.continuousOn
  let b : Fin d → ℝ := fun i => max (a i) (max M 0)
  refine ⟨a, b, ha, fun i => le_max_left _ _, ?_⟩
  intro x hx
  refine ⟨fun i => hlower i x hx, ?_⟩
  intro i
  have hi : x i ≤ M := (le_abs_self _).trans ((norm_le_pi_norm x i).trans (hM x hx))
  exact hi.trans ((le_max_left M 0).trans (le_max_right (a i) _))

/-- Uniform field and Lipschitz bounds on a positive state box and fixed rate box. -/
theorem uniform_mass_action_bounds_box (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (a b : Fin d → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ L K : NNReal,
      (∀ k : R → ℝ, B.Contains k → ∀ x ∈ Icc a b,
        ‖indexedMassAction source target k x‖ ≤ L) ∧
      (∀ k : R → ℝ, B.Contains k →
        LipschitzOnWith K (indexedMassAction source target k) (Icc a b)) := by
  let C : Set ((R → ℝ) × (Fin d → ℝ)) := Icc B.lower B.upper ×ˢ Icc a b
  have hc : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hv : Convex ℝ C := (convex_Icc B.lower B.upper).prod (convex_Icc a b)
  have hd : ContDiffOn ℝ 1 (fun u : (R → ℝ) × (Fin d → ℝ) =>
      indexedMassAction source target u.1 u.2) C :=
    (contDiffOn_indexed_mass_action source target).mono (fun u hu i => (ha i).trans_le (hu.2.1 i))
  obtain ⟨K, hK⟩ := hd.exists_lipschitzOnWith (by norm_num) hv hc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hd.continuousOn
  let L : NNReal := ⟨max M 0, le_max_right _ _⟩
  refine ⟨L, K, ?_, ?_⟩
  · intro k hk x hx
    exact (hM (k, x) ⟨⟨fun e => (hk e).1, fun e => (hk e).2⟩, hx⟩).trans (le_max_left M 0)
  · intro k hk x hx y hy
    have hkC : k ∈ Icc B.lower B.upper := ⟨fun e => (hk e).1, fun e => (hk e).2⟩
    have hh := hK (show (k, x) ∈ C from ⟨hkC, hx⟩) (show (k, y) ∈ C from ⟨hkC, hy⟩)
    simpa only [Prod.edist_eq, edist_self, max_eq_right zero_le] using hh

end EndotacticPermanence.RealComplex
