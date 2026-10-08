module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace EndotacticPermanence

open Function

def dyadicScale (p : ℝ) (n : ℕ) : ℝ := p ^ (2 ^ n)

theorem dyadicScale_pos {p : ℝ} (hp : 0 < p) (n : ℕ) : 0 < dyadicScale p n :=
  pow_pos hp _

theorem dyadicScale_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    dyadicScale p n ≤ p := by
  induction n with
  | zero => simp [dyadicScale]
  | succ n hn =>
    have heq : dyadicScale p (n + 1) = (dyadicScale p n) ^ 2 := by
      simp only [dyadicScale, pow_succ, pow_mul]
    rw [heq]
    have hpos := dyadicScale_pos hp n
    have hprod := mul_nonneg hpos.le (sub_nonneg.mpr (hn.trans hp1.le))
    nlinarith

theorem dyadicScale_succ (p : ℝ) (n : ℕ) :
    dyadicScale p (n + 1) = (dyadicScale p n) ^ 2 := by
  simp only [dyadicScale, pow_succ, pow_mul]

theorem sqrt_dyadicScale_succ {p : ℝ} (hp : 0 < p) (n : ℕ) :
    Real.sqrt (dyadicScale p (n + 1)) = dyadicScale p n := by
  rw [dyadicScale_succ, Real.sqrt_sq (dyadicScale_pos hp n).le]

theorem dyadicScale_tendsto_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (dyadicScale p) Filter.atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hp.le hp1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide))

/-- Finite capped square-root iteration reaches every fixed scale below one.
The auxiliary power sequence makes finiteness explicit. -/
theorem finite_sqrt_chain {h p : ℝ} (hh : 0 < h) (hp1 : p < 1) :
    ∃ n : ℕ, p ≤ h ^ ((1 / 2 : ℝ) ^ n) := by
  have hlim : Filter.Tendsto (fun n : ℕ => h ^ ((1 / 2 : ℝ) ^ n))
      Filter.atTop (nhds 1) := by
    have hz : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [Real.rpow_zero, Function.comp_def] using
      (Real.continuousAt_const_rpow hh.ne').tendsto.comp hz
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hp1)).exists
  exact ⟨n, hn.le⟩

end EndotacticPermanence
