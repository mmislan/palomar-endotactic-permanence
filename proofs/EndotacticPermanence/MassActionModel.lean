module
public import proofs.EndotacticPermanence.Imported.Model
public import proofs.EndotacticPermanence.RateBoxDrift
public import proofs.EndotacticPermanence.MeasurablePicard
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set MeasureTheory
open scoped BigOperators

variable {d : ℕ} {R : Type*} [Fintype R]

def reactionVector (source target : R → Fin d → ℕ) (e : R) : Fin d → ℝ :=
  fun i => (target e i : ℝ) - (source e i : ℝ)

def indexedMassAction (source target : R → Fin d → ℕ)
    (k : R → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  ∑ e, (k e * monomial x (source e)) • reactionVector source target e

def Endotactic (source target : R → Fin d → ℕ) : Prop :=
  ∀ r : Fin d → ℝ, ∀ e, dot r (reactionVector source target e) < 0 →
    ∃ j, 0 < dot r (reactionVector source target j) ∧
      dot r (fun i => (source j i : ℝ)) < dot r (fun i => (source e i : ℝ))

def stoichiometricSubspace (source target : R → Fin d → ℕ) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (reactionVector source target))

def positiveClass (source target : R → Fin d → ℕ) (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | PositiveState x ∧ x - c ∈ stoichiometricSubspace source target}

structure PositiveRateBox (R : Type*) where
  lower : R → ℝ
  upper : R → ℝ
  lower_pos : ∀ e, 0 < lower e
  lower_le_upper : ∀ e, lower e ≤ upper e

def PositiveRateBox.Contains (B : PositiveRateBox R) (k : R → ℝ) : Prop :=
  ∀ e, B.lower e ≤ k e ∧ k e ≤ B.upper e

theorem indexed_mass_action_dot (source target : R → Fin d → ℕ)
    (k : R → ℝ) (x r : Fin d → ℝ) :
    dot r (indexedMassAction source target k x) =
      ∑ e, k e * monomial x (source e) * dot r (reactionVector source target e) := by
  simp only [indexedMassAction, dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measurable_indexed_mass_action (source target : R → Fin d → ℕ)
    (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e)) :
    Measurable (fun tx : ℝ × (Fin d → ℝ) => indexedMassAction source target (k tx.1) tx.2) := by
  unfold indexedMassAction monomial
  fun_prop

theorem indexed_mass_action_mem_span (source target : R → Fin d → ℕ)
    (k : R → ℝ) (x : Fin d → ℝ) :
    indexedMassAction source target k x ∈ stoichiometricSubspace source target := by
  apply Submodule.sum_mem
  intro e _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self e))

end EndotacticPermanence
