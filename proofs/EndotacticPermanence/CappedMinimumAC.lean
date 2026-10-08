module
public import proofs.EndotacticPermanence.ActiveMinimumDrift

@[expose] public section

namespace EndotacticPermanence

open Filter Set MeasureTheory
open scoped Topology

/-- A capped finite AC minimum has nonnegative drift; below its ceiling
the strict all-active drift passes through every tie. -/
theorem ae_capped_min_drift {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) {a b M q : ℝ} (hab : a ≤ b) (hq : 0 ≤ q)
    (hg : AbsolutelyContinuousOnInterval (fun t => s.inf' hs (fun i => f i t)) a b)
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b)
    (hcap : ∀ t, s.inf' hs (fun i => f i t) ≤ M)
    (hd : ∀ᵐ t, t ∈ Icc a b → s.inf' hs (fun i => f i t) < M →
      ∀ i ∈ s, s.inf' hs (fun j => f j t) = f i t → q ≤ deriv (f i) t) :
    ∀ᵐ t, t ∈ Icc a b →
      0 ≤ deriv (fun u => s.inf' hs (fun i => f i u)) t ∧
      (s.inf' hs (fun i => f i t) < M →
        q ≤ deriv (fun u => s.inf' hs (fun i => f i u)) t) := by
  classical
  have hbranches : ∀ᵐ t, ∀ i ∈ s,
      t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    (Filter.eventually_all_finset s).mpr (fun i hi => (hf i hi).ae_differentiableAt)
  filter_upwards [hg.ae_differentiableAt, hbranches, hd] with t ht hb hd htmem
  have hu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using htmem
  by_cases hlt : s.inf' hs (fun i => f i t) < M
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs (fun j => f j t)
    have he := touching_derivative_eq (fun u => Finset.inf'_le (fun j => f j u) hi)
      heq (ht hu).hasDerivAt (hb i hi hu).hasDerivAt
    have hqdr : q ≤ deriv (fun u => s.inf' hs (fun i => f i u)) t := by
      rw [he]
      exact hd htmem hlt i hi heq
    exact ⟨hq.trans hqdr, fun _ => hqdr⟩
  · have heq : s.inf' hs (fun i => f i t) = M := le_antisymm (hcap t) (le_of_not_gt hlt)
    have hm : IsLocalMax (fun u => s.inf' hs (fun i => f i u)) t :=
      Filter.Eventually.of_forall (fun u => by
        change s.inf' hs (fun i => f i u) ≤ s.inf' hs (fun i => f i t)
        rw [heq]
        exact hcap u)
    have hz := hm.hasDerivAt_eq_zero (ht hu).hasDerivAt
    exact ⟨by rw [hz], fun h => False.elim (hlt h)⟩

end EndotacticPermanence
