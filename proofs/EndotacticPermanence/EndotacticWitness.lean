module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace EndotacticPermanence

/- The directional scalar data are the actual projected reaction vectors and
source levels when this lemma is applied to a reaction network. -/
theorem lowest_adverse_witness {R : Type*} [Fintype R]
    (a level : R → ℝ)
    (endo : ∀ e, a e < 0 → ∃ j, 0 < a j ∧ level j < level e)
    (negative : ∃ e, a e < 0) :
    ∃ j, 0 < a j ∧ ∀ e, a e < 0 → level j < level e := by
  classical
  let neg := Finset.univ.filter fun e => a e < 0
  have hneg : neg.Nonempty := by
    obtain ⟨e, he⟩ := negative
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩⟩
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image neg level hneg
  obtain ⟨j, hj, hlevel⟩ := endo e (Finset.mem_filter.mp he).2
  refine ⟨j, hj, ?_⟩
  intro f hf
  exact hlevel.trans_le (hmin f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩))

theorem witness_or_neutral {R : Type*} [Fintype R]
    (a level : R → ℝ)
    (endo : ∀ e, a e < 0 → ∃ j, 0 < a j ∧ level j < level e) :
    (∀ e, a e = 0) ∨
      ∃ j, 0 < a j ∧ ∀ e, a e < 0 → level j < level e := by
  classical
  by_cases hn : ∃ e, a e < 0
  · exact Or.inr (lowest_adverse_witness a level endo hn)
  · by_cases hp : ∃ e, 0 < a e
    · obtain ⟨j, hj⟩ := hp
      exact Or.inr ⟨j, hj, fun e he => False.elim (hn ⟨e, he⟩)⟩
    · left
      intro e
      have h1 : ¬ a e < 0 := fun he => hn ⟨e, he⟩
      have h2 : ¬ 0 < a e := fun he => hp ⟨e, he⟩
      exact le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

end EndotacticPermanence
