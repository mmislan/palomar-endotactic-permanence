module
public import proofs.EndotacticPermanence.FiniteMinAC
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace EndotacticPermanence

open Set MeasureTheory Filter
open scoped BigOperators

/-- Scalar linear comparison at the actual AC/a.e. level. -/
theorem ac_linear_upper {z : ℝ → ℝ} {T ell b : ℝ} (hT : 0 ≤ T)
    (hz : AbsolutelyContinuousOnInterval z 0 T)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → deriv z t ≤ ell * (b - z t)) :
    z T ≤ b + (z 0 - b) * Real.exp (-ell * T) := by
  let w : ℝ → ℝ := fun t => Real.exp (ell * t) * (z t - b)
  have he : AbsolutelyContinuousOnInterval (fun t => Real.exp (ell * t)) 0 T :=
    (show ContDiff ℝ 1 (fun t : ℝ => Real.exp (ell * t)) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hw : AbsolutelyContinuousOnInterval w 0 T :=
    he.fun_mul (hz.sub (LipschitzWith.const b).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hwd : ∀ᵐ t, t ∈ Icc 0 T → deriv w t ≤ 0 := by
    filter_upwards [hz.ae_differentiableAt, hd] with t hzt hdt ht
    have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
    have heD : HasDerivAt (fun s : ℝ => Real.exp (ell * s))
        (ell * Real.exp (ell * t)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul ell).exp
    have hD := heD.mul ((hzt htU).hasDerivAt.sub_const b)
    change HasDerivAt w _ t at hD
    rw [hD.deriv]
    have hp := Real.exp_pos (ell * t)
    nlinarith [hdt ht]
  have hw0 : w 0 = z 0 - b := by simp [w]
  have hdiff : w T ≤ w 0 := by
    have hneg : AbsolutelyContinuousOnInterval (fun t => -w t) 0 T := hw.neg
    have hi := ac_integrated_drift (q := 0) hT hneg (by
      filter_upwards [hw.ae_differentiableAt, hwd] with t hwt hdt ht
      have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
      change 0 ≤ deriv (-w) t
      rw [((hwt htU).hasDerivAt.neg).deriv]
      exact neg_nonneg.mpr (hdt ht))
    linarith
  rw [hw0] at hdiff
  have heq : Real.exp (-ell * T) * Real.exp (ell * T) = 1 := by
    rw [← Real.exp_add]
    have hzero : -ell * T + ell * T = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_left hdiff (Real.exp_pos (-ell * T)).le
  dsimp [w] at hmul
  have hres : z T - b ≤ Real.exp (-ell * T) * (z 0 - b) := by
    rw [← mul_assoc, heq, one_mul] at hmul
    exact hmul
  linarith

/-- Exact polynomial lower bound for exp(3.8), avoiding floating computation. -/
theorem exp_recovery_margin : (128 : ℝ) / 3 < Real.exp (19 / 5) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 19 / 5 by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem recovery_deadline_lt_38 : (10 : ℝ) * Real.log (128 / 3) < 38 := by
  have hlog : Real.log ((128 : ℝ) / 3) < 19 / 5 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr exp_recovery_margin
  linarith

/-! ### Staged recovery certificate for the three-species example

The declarations below formalize the clocked comparison behind the staged
deadline `347/16` of the worked example: composition of an absolutely
continuous path with a map that is Lipschitz on the path's range, the
integrating-factor comparison in an absolutely continuous operational clock,
two-stage clock floors, the inverse-square transformation of a coordinate
obeying the clocked logistic-type equation, and the exact rational roundings.
The fixture-specific derivations of the hypotheses (invariance of the startup
box, construction of the clocks, and the Riccati comparison for the first
coordinate) are conventional and are not formalized here. -/

/-- Composition of an absolutely continuous path with a map that is Lipschitz
on a set containing the path's values on the interval. -/
theorem lipschitzOn_comp_ac {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : X → Y} {x : ℝ → X} {K : NNReal} {a b : ℝ} {s : Set X}
    (hF : LipschitzOnWith K F s) (hmaps : ∀ t ∈ uIcc a b, x t ∈ s)
    (hx : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun t => F (x t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hx ⊢
  intro ε hε
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, h⟩ := hx (ε / ((K : ℝ) + 1)) (div_pos hε hKpos)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hsum := h E hE hlen
  have hmem : ∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b := by
    simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_setOf_eq] at hE
    intro i hi
    exact hE.1 i (by simpa using hi)
  calc ∑ i ∈ Finset.range E.1, dist (F (x (E.2 i).1)) (F (x (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (x (E.2 i).1) (x (E.2 i).2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact hF.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (x (E.2 i).1) (x (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum.le (NNReal.coe_nonneg K)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hKpos]
        nlinarith [NNReal.coe_nonneg K]

/-- Clocked AC linear comparison: if the a.e. derivative of `z` is at most the
clock speed `deriv σ` times `(b - z)`, then `z` is bounded by the
integrating-factor envelope evaluated at the accumulated clock `σ T - σ 0`.
Only absolute continuity of the clock is used. -/
theorem ac_clocked_linear_upper {z σ : ℝ → ℝ} {T b : ℝ} (hT : 0 ≤ T)
    (hz : AbsolutelyContinuousOnInterval z 0 T)
    (hσ : AbsolutelyContinuousOnInterval σ 0 T)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → deriv z t ≤ deriv σ t * (b - z t)) :
    z T ≤ b + (z 0 - b) * Real.exp (σ 0 - σ T) := by
  have hcont : ContinuousOn σ (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hσ.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  have hσM : ∀ t ∈ Icc 0 T, σ t ≤ M := fun t ht => hM ⟨t, ht, rfl⟩
  have hlip : LipschitzOnWith (Real.exp M).toNNReal Real.exp (Iic M) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [Real.coe_toNNReal _ (Real.exp_pos M).le, Real.dist_eq, Real.dist_eq]
    have hbound : ∀ w ∈ Iic M, ‖deriv Real.exp w‖ ≤ Real.exp M := fun w hw => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos w)]
      exact Real.exp_le_exp.mpr hw
    have hmv := (convex_Iic M).norm_image_sub_le_of_norm_deriv_le
      (fun w _ => Real.differentiableAt_exp) hbound hv hu
    simpa only [Real.norm_eq_abs] using hmv
  have hE : AbsolutelyContinuousOnInterval (fun t => Real.exp (σ t)) 0 T :=
    lipschitzOn_comp_ac hlip
      (fun t ht => hσM t (by simpa only [uIcc_of_le hT] using ht)) hσ
  let w : ℝ → ℝ := fun t => Real.exp (σ t) * (z t - b)
  have hw : AbsolutelyContinuousOnInterval w 0 T :=
    hE.fun_mul (hz.sub (LipschitzWith.const b).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hwd : ∀ᵐ t, t ∈ Icc 0 T → deriv w t ≤ 0 := by
    filter_upwards [hz.ae_differentiableAt, hσ.ae_differentiableAt, hd] with t hzt hσt hdt ht
    have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
    have heD : HasDerivAt (fun s : ℝ => Real.exp (σ s)) (Real.exp (σ t) * deriv σ t) t :=
      (hσt htU).hasDerivAt.exp
    have hD := heD.mul ((hzt htU).hasDerivAt.sub_const b)
    change HasDerivAt w _ t at hD
    rw [hD.deriv]
    have hp := Real.exp_pos (σ t)
    have hin : deriv σ t * (z t - b) + deriv z t ≤ 0 := by
      have h1 := hdt ht
      have h2 : deriv σ t * (z t - b) = -(deriv σ t * (b - z t)) := by ring
      linarith
    have hfac : Real.exp (σ t) * deriv σ t * (z t - b) + Real.exp (σ t) * deriv z t
        = Real.exp (σ t) * (deriv σ t * (z t - b) + deriv z t) := by ring
    rw [hfac]
    exact mul_nonpos_iff.mpr (Or.inl ⟨hp.le, hin⟩)
  have hdiff : w T ≤ w 0 := by
    have hneg : AbsolutelyContinuousOnInterval (fun t => -w t) 0 T := hw.neg
    have hi := ac_integrated_drift (q := 0) hT hneg (by
      filter_upwards [hw.ae_differentiableAt, hwd] with t hwt hdt ht
      have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
      change 0 ≤ deriv (-w) t
      rw [((hwt htU).hasDerivAt.neg).deriv]
      exact neg_nonneg.mpr (hdt ht))
    linarith
  have hpos := Real.exp_pos (σ T)
  have hkey : (z T - b) * Real.exp (σ T) ≤ (z 0 - b) * Real.exp (σ 0) := by
    dsimp only [w] at hdiff
    linarith
  have h3 : z T - b ≤ (z 0 - b) * (Real.exp (σ 0) / Real.exp (σ T)) := by
    rw [← mul_div_assoc, le_div_iff₀ hpos]
    exact hkey
  rw [Real.exp_sub]
  linarith

/-- Two-stage clock floor: speed at least `v₁` up to `t₁` and at least `v₂`
afterwards gives the stated accumulated clock. -/
theorem ac_clock_two_stage {σ : ℝ → ℝ} {t₁ T v₁ v₂ : ℝ} (h0 : 0 ≤ t₁) (h1 : t₁ ≤ T)
    (hσ : AbsolutelyContinuousOnInterval σ 0 T)
    (hv1 : ∀ᵐ t, t ∈ Icc 0 t₁ → v₁ ≤ deriv σ t)
    (hv2 : ∀ᵐ t, t ∈ Icc t₁ T → v₂ ≤ deriv σ t) :
    σ 0 + v₁ * t₁ + v₂ * (T - t₁) ≤ σ T := by
  have hT : 0 ≤ T := h0.trans h1
  have hs1 : AbsolutelyContinuousOnInterval σ 0 t₁ :=
    hσ.mono (by rw [uIcc_of_le h0, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl h1)
  have hs2 : AbsolutelyContinuousOnInterval σ t₁ T :=
    hσ.mono (by rw [uIcc_of_le h1, uIcc_of_le hT]; exact Icc_subset_Icc h0 le_rfl)
  have e1 := ac_integrated_drift h0 hs1 hv1
  have e2 := ac_integrated_drift h1 hs2 hv2
  simp only [sub_zero] at e1
  linarith

/-- Staged recovery of an inverse-square observable `z`. Hypotheses: the a.e.
clocked inequality `z' ≤ σ'(4 - z)`, the startup bound `z 0 ≤ 100`, clock speed
at least `1/10` before `t₁` and at least `2/5` after it, and the arithmetic
condition that the accumulated clock reaches `19/5` by `t₂`. Conclusion:
`z ≤ 25/4` from `t₂` on. -/
theorem staged_inverse_square_recovery {z σ : ℝ → ℝ} {t₁ t₂ : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hz : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval z 0 T)
    (hσ : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval σ 0 T)
    (hσ0 : σ 0 = 0) (hz0 : z 0 ≤ 100)
    (hv1 : ∀ᵐ t, t ∈ Icc 0 t₁ → 1 / 10 ≤ deriv σ t)
    (hv2 : ∀ᵐ t, t₁ ≤ t → 2 / 5 ≤ deriv σ t)
    (hd : ∀ᵐ t, 0 ≤ t → deriv z t ≤ deriv σ t * (4 - z t))
    (hstage : 19 / 5 ≤ t₁ / 10 + 2 / 5 * (t₂ - t₁)) (t : ℝ) (ht : t₂ ≤ t) :
    z t ≤ 25 / 4 := by
  have h1t : t₁ ≤ t := h12.trans ht
  have hT : 0 ≤ t := h0.trans h1t
  have hclock : 19 / 5 ≤ σ t := by
    have := ac_clock_two_stage h0 h1t (hσ t hT) hv1
      (by filter_upwards [hv2] with s hs hs'; exact hs hs'.1)
    rw [hσ0] at this
    linarith
  have hcmp := ac_clocked_linear_upper hT (hz t hT) (hσ t hT)
    (by filter_upwards [hd] with s hs hs'; exact hs hs'.1)
  rw [hσ0, zero_sub] at hcmp
  have hexp : Real.exp (-σ t) ≤ Real.exp (-(19 / 5)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsmall : 96 * Real.exp (-(19 / 5)) < 9 / 4 := by
    have hp := Real.exp_pos (19 / 5)
    have hinv : Real.exp (-(19 / 5)) = (Real.exp (19 / 5))⁻¹ := Real.exp_neg _
    rw [hinv, ← div_eq_mul_inv, div_lt_iff₀ hp]
    linarith [exp_recovery_margin]
  rcases le_or_gt (z 0) 4 with hz4 | hz4
  · have : (z 0 - 4) * Real.exp (-σ t) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨by linarith, (Real.exp_pos _).le⟩)
    linarith
  · have h96 : (z 0 - 4) * Real.exp (-σ t) ≤ 96 * Real.exp (-(19 / 5)) :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by norm_num)
    linarith

/-- Derivative of the inverse square at a positive point. -/
theorem inv_sq_hasDerivAt {y : ℝ} (hypos : 0 < y) :
    HasDerivAt (fun v : ℝ => (v * v)⁻¹) (-(2 / y ^ 3)) y := by
  have hD : HasDerivAt (fun v : ℝ => (v * v)⁻¹) (-(1 * y + y * 1) / (y * y) ^ 2) y :=
    ((hasDerivAt_id' y).mul (hasDerivAt_id' y)).inv (mul_pos hypos hypos).ne'
  have hne : y ≠ 0 := hypos.ne'
  have hval : -(1 * y + y * 1) / (y * y) ^ 2 = -(2 / y ^ 3) := by
    field_simp
    ring
  rw [hval] at hD
  exact hD

/-- Derivative bound for the inverse square on `[1/10, 10]`. -/
theorem inv_sq_deriv_bound {y : ℝ} (hy : y ∈ Icc (1 / 10 : ℝ) 10) :
    ‖deriv (fun v : ℝ => (v * v)⁻¹) y‖ ≤ 2000 := by
  have hypos : 0 < y := by linarith [hy.1]
  have hp3 : 0 < y ^ 3 := pow_pos hypos 3
  rw [(inv_sq_hasDerivAt hypos).deriv, Real.norm_eq_abs, abs_neg,
    abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hp3), div_le_iff₀ hp3]
  have h3 : (1 / 10 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy.1 3
  have hpow : (1 / 10 : ℝ) ^ 3 = 1 / 1000 := by norm_num
  rw [hpow] at h3
  linarith

/-- The inverse square is Lipschitz on `[1/10, 10]`. -/
theorem inv_sq_lipschitzOn :
    LipschitzOnWith (2000 : NNReal) (fun v : ℝ => (v * v)⁻¹) (Icc (1 / 10 : ℝ) 10) := by
  refine LipschitzOnWith.of_dist_le_mul fun v hv w hw => ?_
  have hcoe : ((2000 : NNReal) : ℝ) = 2000 := by norm_num
  rw [hcoe, Real.dist_eq, Real.dist_eq]
  have hmv := (convex_Icc (1 / 10 : ℝ) 10).norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (inv_sq_hasDerivAt (by linarith [hy.1] : (0 : ℝ) < y)).differentiableAt)
    (fun y hy => inv_sq_deriv_bound hy) hw hv
  simpa only [Real.norm_eq_abs] using hmv

/-- The inverse square of a coordinate confined to `[1/10, 10]` is absolutely
continuous along an absolutely continuous path. -/
theorem inverse_square_ac {u : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hbox : ∀ t ∈ Icc 0 T, 1 / 10 ≤ u t ∧ u t ≤ 10) :
    AbsolutelyContinuousOnInterval (fun t => (u t * u t)⁻¹) 0 T := by
  have hmaps : ∀ t ∈ uIcc (0 : ℝ) T, u t ∈ Icc (1 / 10 : ℝ) 10 := fun t ht =>
    Set.mem_Icc.mpr (hbox t (by simpa only [uIcc_of_le hT] using ht))
  have h := lipschitzOn_comp_ac inv_sq_lipschitzOn hmaps hu
  exact h

/-- Staged recovery of one coordinate of the fixture in clock form. `u` is the
coordinate (`b` or `c`), `σ` its operational clock (`∫a` or `∫b`, with
`deriv σ` the clock speed), and `kp, km` its two coefficients. Hypotheses: the
invariant startup box, the a.e. clocked equation `u' = σ' u (kp - km u²)`, the
coefficient box, nonnegative clock speed, and the two clock floors. -/
theorem staged_coordinate_recovery {u σ kp km : ℝ → ℝ} {t₁ t₂ : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hu : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T)
    (hσ : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval σ 0 T)
    (hσ0 : σ 0 = 0)
    (hbox : ∀ t, 0 ≤ t → 1 / 10 ≤ u t ∧ u t ≤ 10)
    (hk : ∀ t, 1 / 2 ≤ kp t ∧ km t ≤ 2)
    (hσpos : ∀ᵐ t, 0 ≤ t → 0 ≤ deriv σ t)
    (hode : ∀ᵐ t, 0 ≤ t → HasDerivAt u (deriv σ t * u t * (kp t - km t * u t ^ 2)) t)
    (hv1 : ∀ᵐ t, t ∈ Icc 0 t₁ → 1 / 10 ≤ deriv σ t)
    (hv2 : ∀ᵐ t, t₁ ≤ t → 2 / 5 ≤ deriv σ t)
    (hstage : 19 / 5 ≤ t₁ / 10 + 2 / 5 * (t₂ - t₁)) (t : ℝ) (ht : t₂ ≤ t) :
    2 / 5 ≤ u t := by
  let z : ℝ → ℝ := fun s => (u s * u s)⁻¹
  have hz : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval z 0 T := fun T hT =>
    inverse_square_ac hT (hu T hT) (fun s hs => hbox s hs.1)
  have hz0 : z 0 ≤ 100 := by
    have h0pos : 0 < u 0 := by linarith [(hbox 0 le_rfl).1]
    show (u 0 * u 0)⁻¹ ≤ 100
    rw [inv_le_comm₀ (mul_pos h0pos h0pos) (by norm_num)]
    norm_num
    nlinarith [(hbox 0 le_rfl).1]
  have hd : ∀ᵐ t, 0 ≤ t → deriv z t ≤ deriv σ t * (4 - z t) := by
    filter_upwards [hσpos, hode] with t hσt hut ht
    have hupos : 0 < u t := by linarith [(hbox t ht).1]
    have hne : u t ≠ 0 := hupos.ne'
    have hD : HasDerivAt z
        (-(deriv σ t * u t * (kp t - km t * u t ^ 2) * u t
          + u t * (deriv σ t * u t * (kp t - km t * u t ^ 2))) / (u t * u t) ^ 2) t :=
      ((hut ht).mul (hut ht)).inv (mul_pos hupos hupos).ne'
    rw [hD.deriv]
    show _ ≤ deriv σ t * (4 - (u t * u t)⁻¹)
    have hzpos : 0 < (u t * u t)⁻¹ := inv_pos.mpr (mul_pos hupos hupos)
    have hid : -(deriv σ t * u t * (kp t - km t * u t ^ 2) * u t
          + u t * (deriv σ t * u t * (kp t - km t * u t ^ 2))) / (u t * u t) ^ 2
        = deriv σ t * (-2 * kp t * (u t * u t)⁻¹ + 2 * km t) := by
      field_simp
      ring
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ (hσt ht)
    nlinarith [mul_nonneg (by linarith [(hk t).1] : (0 : ℝ) ≤ 2 * kp t - 1) hzpos.le, (hk t).2]
  have hzt : (u t * u t)⁻¹ ≤ 25 / 4 :=
    staged_inverse_square_recovery h0 h12 hz hσ hσ0 hz0 hv1 hv2 hd hstage t ht
  have hupos : 0 < u t := by linarith [(hbox t (h0.trans (h12.trans ht))).1]
  rw [inv_le_comm₀ (mul_pos hupos hupos) (by norm_num)] at hzt
  norm_num at hzt
  nlinarith [hzt, hupos]

/-- Exact rational lower bound for `exp(9/5)`. -/
theorem exp_nine_fifths_gt_six : (6 : ℝ) < Real.exp (9 / 5) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 5 by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- The first-coordinate deadline `5 log 6` is below `9`. -/
theorem a_stage_deadline_lt_nine : (5 : ℝ) * Real.log 6 < 9 := by
  have hlog : Real.log (6 : ℝ) < 9 / 5 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr exp_nine_fifths_gt_six
  linarith

/-- Stage for the second coordinate: clock switch at `9`, deadline `65/4`. -/
theorem staged_recovery_second {u σ kp km : ℝ → ℝ}
    (hu : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T)
    (hσ : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval σ 0 T)
    (hσ0 : σ 0 = 0)
    (hbox : ∀ t, 0 ≤ t → 1 / 10 ≤ u t ∧ u t ≤ 10)
    (hk : ∀ t, 1 / 2 ≤ kp t ∧ km t ≤ 2)
    (hσpos : ∀ᵐ t, 0 ≤ t → 0 ≤ deriv σ t)
    (hode : ∀ᵐ t, 0 ≤ t → HasDerivAt u (deriv σ t * u t * (kp t - km t * u t ^ 2)) t)
    (hv1 : ∀ᵐ t, t ∈ Icc 0 9 → 1 / 10 ≤ deriv σ t)
    (hv2 : ∀ᵐ t, (9 : ℝ) ≤ t → 2 / 5 ≤ deriv σ t) (t : ℝ) (ht : 65 / 4 ≤ t) :
    2 / 5 ≤ u t :=
  staged_coordinate_recovery (by norm_num) (by norm_num) hu hσ hσ0 hbox hk hσpos hode hv1 hv2
    (by norm_num) t ht

/-- Stage for the third coordinate: clock switch at `65/4`, deadline `347/16`. -/
theorem staged_recovery_third {u σ kp km : ℝ → ℝ}
    (hu : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T)
    (hσ : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval σ 0 T)
    (hσ0 : σ 0 = 0)
    (hbox : ∀ t, 0 ≤ t → 1 / 10 ≤ u t ∧ u t ≤ 10)
    (hk : ∀ t, 1 / 2 ≤ kp t ∧ km t ≤ 2)
    (hσpos : ∀ᵐ t, 0 ≤ t → 0 ≤ deriv σ t)
    (hode : ∀ᵐ t, 0 ≤ t → HasDerivAt u (deriv σ t * u t * (kp t - km t * u t ^ 2)) t)
    (hv1 : ∀ᵐ t, t ∈ Icc 0 (65 / 4) → 1 / 10 ≤ deriv σ t)
    (hv2 : ∀ᵐ t, (65 / 4 : ℝ) ≤ t → 2 / 5 ≤ deriv σ t) (t : ℝ) (ht : 347 / 16 ≤ t) :
    2 / 5 ≤ u t :=
  staged_coordinate_recovery (by norm_num) (by norm_num) hu hσ hσ0 hbox hk hσpos hode hv1 hv2
    (by norm_num) t ht

/-- The rounded staged deadline. -/
theorem staged_deadline_lt_22 : (347 : ℝ) / 16 < 22 := by norm_num

end EndotacticPermanence
