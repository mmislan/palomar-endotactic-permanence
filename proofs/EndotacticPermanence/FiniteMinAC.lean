module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace EndotacticPermanence

open Filter Set MeasureTheory
open scoped Topology

/-- The finite affine minimum remains absolutely continuous along an AC path
because it is Lipschitz; the argument applies to any Lipschitz observable. -/
theorem lipschitz_comp_ac {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : X → Y} {x : ℝ → X} {K : NNReal} {a b : ℝ}
    (hF : LipschitzWith K F) (hx : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun t => F (x t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hx ⊢
  have hbound := Filter.Tendsto.const_mul (K : ℝ) hx
  simp only [mul_zero] at hbound
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun _ => ?_) hbound
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => hF.dist_le_mul _ _

theorem lipschitz_finset_min {X ι : Type*} [PseudoMetricSpace X]
    (K : NNReal) (f : ι → X → ℝ) (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) :
    LipschitzWith K (fun x => s.inf' hs (fun i => f i x)) := by
  classical
  revert hs hf
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
      intro hs hf
      by_cases hne : s.Nonempty
      · have hfi := hf i (Finset.mem_insert_self i s)
        have hfs := ih hne (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        simpa only [Finset.inf'_insert hne, max_self] using hfi.min hfs
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst s
        simpa using hf i (Finset.mem_insert_self i ∅)

/-- At an ordinary differentiability time, a differentiable branch touching a
differentiable lower envelope has the same derivative. This handles ties
without choosing one branch before knowing the full active set. -/
theorem touching_derivative_eq {g f : ℝ → ℝ} {t dg df : ℝ}
    (hle : ∀ s, g s ≤ f s) (heq : g t = f t)
    (hg : HasDerivAt g dg t) (hf : HasDerivAt f df t) : dg = df := by
  have hmin : IsLocalMin (fun s => f s - g s) t := by
    apply Filter.Eventually.of_forall
    intro s
    change f t - g t ≤ f s - g s
    rw [heq, sub_self]
    exact sub_nonneg.mpr (hle s)
  have hz := hmin.hasDerivAt_eq_zero (hf.sub hg)
  linarith

/-- Almost-everywhere drift integrates for AC observables, including histories
whose rates are only measurable. -/
theorem ac_integrated_drift {g : ℝ → ℝ} {a b q : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → q ≤ deriv g t) :
    q * (b - a) ≤ g b - g a := by
  have hrestr : (fun _ : ℝ => q) ≤ᵐ[volume.restrict (Icc a b)] deriv g := by
    change ∀ᵐ t ∂volume.restrict (Icc a b), q ≤ deriv g t
    rw [ae_restrict_iff' measurableSet_Icc]
    exact hd
  have h := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q) volume a b)
    hg.intervalIntegrable_deriv hrestr
  rw [intervalIntegral.integral_const, smul_eq_mul, hg.integral_deriv_eq_sub] at h
  simpa only [mul_comm] using h

end EndotacticPermanence
