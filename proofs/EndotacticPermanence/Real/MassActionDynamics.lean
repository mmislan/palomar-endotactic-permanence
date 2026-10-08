module
public import proofs.EndotacticPermanence.Real.EndotacticTrapping
public import proofs.EndotacticPermanence.TailFiniteEntryAC

@[expose] public section

namespace EndotacticPermanence.RealComplex

noncomputable section

open OAI.Problem326 Set Filter MeasureTheory

variable {d : ℕ} {R : Type*} [Fintype R]

theorem mass_action_curve_in_class (source target : R → Fin d → ℝ)
    (k : ℝ → R → ℝ) {c x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx0 : x0 - c ∈ stoichiometricSubspace source target)
    (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x) :
    ∀ t : ℝ, 0 ≤ t → x t - c ∈ stoichiometricSubspace source target := by
  intro t ht
  have h := hx.2.1 t ht
  rw [h.2 t ⟨ht, le_rfl⟩]
  have hi := interval_integral_mem_submodule (stoichiometricSubspace source target) h.1
    (fun u => indexed_mass_action_mem_span source target (k u) (x u))
  have heq : x0 + (∫ u in (0 : ℝ)..t, indexedMassAction source target (k u) (x u)) - c =
      (x0 - c) + ∫ u in (0 : ℝ)..t, indexedMassAction source target (k u) (x u) := by abel
  rw [heq]
  exact Submodule.add_mem _ hx0 hi

theorem mass_action_finite_entry (source target : R → Fin d → ℝ)
    (B : PositiveRateBox R) (G : GeometricFamily d (sourceComparisons source))
    (c : Fin d → ℝ) (a : ℝ) (ha : 0 ≤ a) {h : ℝ} {j0 : Fin G.n} {K : Set (Fin d → ℝ)}
    {δ A : ℝ} (hδ : 0 < δ) (hz : G.slope j0 = 0)
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0)
    (hmargin : ∀ x ∈ positiveClass source target c,
      x ∈ Icc (fun _ => h) (fun _ => h⁻¹) → x ∉ K →
        ∀ j, AffineActive G.slope (fun k => G.offset k h) x j →
          ∀ k : R → ℝ, B.Contains k →
            δ ≤ dot (G.slope j) (indexedMassAction source target k x))
    (k : ℝ → R → ℝ) (hkbox : ∀ t : ℝ, 0 ≤ t → B.Contains (k t))
    {x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardCaratheodoryCurve (fun t => indexedMassAction source target (k t)) x0 x)
    (hxclass : ∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c)
    (hxbox : ∀ t : ℝ, a ≤ t → x t ∈ Icc (fun _ => h) (fun _ => h⁻¹))
    (hA : A ≤ G.envelope h (x a)) :
    a ≤ a + (G.offset j0 h - A) / δ + 1 ∧
      ∀ t : ℝ, a + (G.offset j0 h - A) / δ + 1 ≤ t → x t ∈ K := by
  have hac (T : ℝ) (hT : a ≤ T) : AbsolutelyContinuousOnInterval x a T := by
    apply (hx.2.2.1 T (ha.trans hT)).mono
    rw [uIcc_of_le hT, uIcc_of_le (ha.trans hT)]
    exact Icc_subset_Icc_left ha
  have hd (T : ℝ) (hT : a ≤ T) :
      ∀ᵐ t, t ∈ Icc a T → x t ∉ K →
        ∀ j, AffineActive G.slope (fun k => G.offset k h) (x t) j →
          δ ≤ deriv (fun u => dot (G.slope j) (x u) + G.offset j h) t := by
    filter_upwards [hx.2.2.2 T (ha.trans hT), volume.ae_ne 0, volume.ae_ne T] with t ht hn0 hnT htmem hnot j hj
    have hti : t ∈ Ioo 0 T :=
      ⟨lt_of_le_of_ne (ha.trans htmem.1) (Ne.symm hn0), lt_of_le_of_ne htmem.2 hnT⟩
    rw [(affine_branch_hasDerivAt (G.slope j) (G.offset j h) (ht hti)).deriv]
    exact hmargin (x t) (hxclass t (ha.trans htmem.1)) (hxbox t htmem.1) hnot j hj (k t) (hkbox t (ha.trans htmem.1))
  have hm (T : ℝ) (hT : a ≤ T) :=
    G.envelope_monotone h hz hK hT hδ.le (hac T hT) (hd T hT)
  have hcap (t : ℝ) (_ht : a ≤ t) : G.envelope h (x t) ≤ G.offset j0 h := by
    simpa [hz, dot] using G.envelope_le h (x t) j0
  have hdr (T : ℝ) (hT : a ≤ T) : ∀ᵐ t, t ∈ Icc a T →
      G.envelope h (x t) < G.offset j0 h →
        δ ≤ deriv (fun u => G.envelope h (x u)) t := by
    filter_upwards [(hm T hT).2] with t ht htmem hlt
    apply ht htmem
    intro hk
    exact (ne_of_lt hlt) ((G.plateau_eq_ceiling h hz hK (x t)).mp hk)
  have hh := finite_entry_on_tail (A := A) hδ hA hcap
    (fun T hT => G.envelope_ac h (hac T hT))
    (fun T hT => (hm T hT).1) hdr
  exact ⟨hh.1, fun t ht => (G.plateau_eq_ceiling h hz hK (x t)).mpr (hh.2 t ht)⟩

end
end EndotacticPermanence.RealComplex
