module
public import proofs.EndotacticPermanence.Real.Monomial
public import proofs.EndotacticPermanence.CaratheodoryInterface
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw

@[expose] public section

namespace EndotacticPermanence.RealComplex

open OAI.Problem326 Set MeasureTheory
open scoped BigOperators

noncomputable section
variable {d : ℕ} {R : Type*} [Fintype R]

/-- Reaction vectors for arbitrary real source and target complexes. -/
def reactionVector (source target : R → Fin d → ℝ) (e : R) : Fin d → ℝ :=
  target e - source e

/-- Real-exponent mass-action field on the positive orthant. -/
def indexedMassAction (source target : R → Fin d → ℝ)
    (k : R → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  ∑ e, (k e * monomial x (source e)) • reactionVector source target e

/-- Ordinary endotacticity: every adverse reaction has a strictly earlier
source whose reaction points into the tested direction. Neutral reactions
are allowed; witnesses need not be at globally minimal sources. -/
def Endotactic (source target : R → Fin d → ℝ) : Prop :=
  ∀ r : Fin d → ℝ, ∀ e, dot r (reactionVector source target e) < 0 →
    ∃ j, 0 < dot r (reactionVector source target j) ∧ dot r (source j) < dot r (source e)

def stoichiometricSubspace (source target : R → Fin d → ℝ) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (reactionVector source target))

def positiveClass (source target : R → Fin d → ℝ) (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | PositiveState x ∧ x - c ∈ stoichiometricSubspace source target}

theorem indexed_mass_action_dot (source target : R → Fin d → ℝ)
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

theorem measurable_indexed_mass_action (source target : R → Fin d → ℝ)
    (k : ℝ → R → ℝ) (hk : ∀ e, Measurable (fun t => k t e)) :
    Measurable (fun tx : ℝ × (Fin d → ℝ) => indexedMassAction source target (k tx.1) tx.2) := by
  unfold indexedMassAction monomial
  fun_prop

theorem indexed_mass_action_mem_span (source target : R → Fin d → ℝ)
    (k : R → ℝ) (x : Fin d → ℝ) :
    indexedMassAction source target k x ∈ stoichiometricSubspace source target := by
  apply Submodule.sum_mem
  intro e _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self e))

theorem indexed_mass_action_nat_agreement (source target : R → Fin d → ℕ)
    (k : R → ℝ) {x : Fin d → ℝ} (hx : PositiveState x) :
    indexedMassAction (fun e i => (source e i : ℝ)) (fun e i => (target e i : ℝ)) k x =
      EndotacticPermanence.indexedMassAction source target k x := by
  unfold indexedMassAction EndotacticPermanence.indexedMassAction
  apply Finset.sum_congr rfl
  intro e _
  rw [monomial_nat_agreement hx]
  rfl

omit [Fintype R] in
theorem endotactic_nat_embedding (source target : R → Fin d → ℕ)
    (h : EndotacticPermanence.Endotactic source target) :
    Endotactic (fun e i => (source e i : ℝ)) (fun e i => (target e i : ℝ)) := by
  exact h

end
end EndotacticPermanence.RealComplex
