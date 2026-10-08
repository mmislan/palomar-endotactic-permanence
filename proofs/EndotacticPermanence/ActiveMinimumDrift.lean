module
public import proofs.EndotacticPermanence.FiniteMinAC

@[expose] public section

namespace EndotacticPermanence

open Filter Set MeasureTheory

/-- Every tied minimizing branch transfers its drift to the AC minimum at
almost every time. This requires no continuously differentiable rate history. -/
theorem ae_finset_min_drift {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) {a b q : ℝ} (hab : a ≤ b)
    (hg : AbsolutelyContinuousOnInterval (fun t => s.inf' hs (fun i => f i t)) a b)
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → ∀ i ∈ s,
      s.inf' hs (fun j => f j t) = f i t → q ≤ deriv (f i) t) :
    ∀ᵐ t, t ∈ Icc a b → q ≤ deriv (fun t => s.inf' hs (fun i => f i t)) t := by
  classical
  have hbranches : ∀ᵐ t, ∀ i ∈ s,
      t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    (Filter.eventually_all_finset s).mpr (fun i hi => (hf i hi).ae_differentiableAt)
  filter_upwards [hg.ae_differentiableAt, hbranches, hd] with t ht hb hd htmem
  have hu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using htmem
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs (fun j => f j t)
  have he : deriv (fun t => s.inf' hs (fun j => f j t)) t = deriv (f i) t :=
    touching_derivative_eq (fun u => Finset.inf'_le (fun j => f j u) hi) heq
      (ht hu).hasDerivAt (hb i hi hu).hasDerivAt
  rw [he]
  exact hd htmem i hi heq

theorem ac_finset_min_integrated_drift {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) {a b q : ℝ} (hab : a ≤ b)
    (hg : AbsolutelyContinuousOnInterval (fun t => s.inf' hs (fun i => f i t)) a b)
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → ∀ i ∈ s,
      s.inf' hs (fun j => f j t) = f i t → q ≤ deriv (f i) t) :
    q * (b - a) ≤ s.inf' hs (fun i => f i b) - s.inf' hs (fun i => f i a) :=
  ac_integrated_drift hab hg (ae_finset_min_drift s hs f hab hg hf hd)

end EndotacticPermanence
