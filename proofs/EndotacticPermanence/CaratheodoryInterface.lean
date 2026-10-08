module
public import proofs.EndotacticPermanence.EndotacticTrapping
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

namespace EndotacticPermanence

open Set Filter MeasureTheory

def IsCaratheodorySolution {d : ℕ} (f : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (x0 : Fin d → ℝ) (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval x 0 T) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (f t (x t)) t)

/-- The integral formulation in the root is equivalent to initial data,
local absolute continuity and the a.e. ODE alone. -/
theorem forward_curve_of_ac_ode {d : ℕ} {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    {x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)} (hx0 : x 0 = x0)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval x 0 T)
    (hode : ∀ T : ℝ, 0 ≤ T → ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (f t (x t)) t) :
    IsForwardCaratheodoryCurve f x0 x := by
  refine ⟨hx0, ?_, hac, hode⟩
  intro T hT
  have hc (i : Fin d) : AbsolutelyContinuousOnInterval (fun t => x t i) 0 T :=
    lipschitz_comp_ac (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).lipschitzWith (hac T hT)
  have hd (i : Fin d) : ∀ᵐ t, t ∈ Icc 0 T → deriv (fun u => x u i) t = f t (x t) i := by
    filter_upwards [hode T hT, volume.ae_ne 0, volume.ae_ne T] with t ht hn0 hnT htmem
    have hti : t ∈ Ioo 0 T :=
      ⟨lt_of_le_of_ne htmem.1 (Ne.symm hn0), lt_of_le_of_ne htmem.2 hnT⟩
    exact (hasDerivAt_pi.mp (ht hti) i).deriv
  have hci (i : Fin d) : IntervalIntegrable (fun t => f t (x t) i) volume 0 T := by
    apply (hc i).intervalIntegrable_deriv.congr_ae
    filter_upwards [ae_restrict_of_ae (hd i), ae_restrict_mem measurableSet_uIoc] with t ht htmem
    apply ht
    simpa only [uIcc_of_le hT] using uIoc_subset_uIcc htmem
  have hint : IntervalIntegrable (fun t => f t (x t)) volume 0 T := by
    exact ⟨Integrable.of_eval (fun i => (hci i).1), Integrable.of_eval (fun i => (hci i).2)⟩
  refine ⟨hint, ?_⟩
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2
  have hit := hint.mono_set hsub
  funext i
  have hcomm := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hit
  change (∫ u in (0 : ℝ)..t, f u (x u) i) = (∫ u in (0 : ℝ)..t, f u (x u)) i at hcomm
  have heq : (∫ u in (0 : ℝ)..t, f u (x u) i) = x t i - x 0 i := by
    have hFTC := ((hc i).mono hsub).integral_deriv_eq_sub
    rw [← hFTC]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd i] with u hu humem
    exact (hu (by
      have hucc : u ∈ Icc 0 t := by
        simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc humem
      exact ⟨hucc.1, hucc.2.trans ht.2⟩)).symm
  change x t i = x0 i + (∫ u in (0 : ℝ)..t, f u (x u)) i
  rw [← hcomm, heq, hx0]
  ring

theorem forward_curve_iff_ac_ode {d : ℕ} {f : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    {x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)} :
    IsForwardCaratheodoryCurve f x0 x ↔ IsCaratheodorySolution f x0 x := by
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
  · intro hx
    exact forward_curve_of_ac_ode hx.1 hx.2.1 hx.2.2

end EndotacticPermanence
