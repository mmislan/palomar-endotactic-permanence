module
public import proofs.EndotacticPermanence.AffineObservable
public import proofs.EndotacticPermanence.Imported.PlateauGeometry

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set Filter MeasureTheory
open scoped Topology BigOperators

variable {d : ℕ} {D : Finset (Fin d → ℝ)}

theorem GeometricFamily.plateau_eq_ceiling (G : GeometricFamily d D) (h : ℝ)
    {j0 : Fin G.n} (hz : G.slope j0 = 0) {K : Set (Fin d → ℝ)}
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0) (x : Fin d → ℝ) :
    x ∈ K ↔ G.envelope h x = G.offset j0 h := by
  rw [hK x, ← G.envelope_eq_iff]
  simp [hz, dot]

theorem GeometricFamily.envelope_monotone (G : GeometricFamily d D) (h : ℝ)
    {j0 : Fin G.n} (hz : G.slope j0 = 0) {K : Set (Fin d → ℝ)}
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0)
    {x : ℝ → (Fin d → ℝ)} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hx : AbsolutelyContinuousOnInterval x a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → x t ∉ K →
      ∀ j, AffineActive G.slope (fun k => G.offset k h) (x t) j →
        δ ≤ deriv (fun u => dot (G.slope j) (x u) + G.offset j h) t) :
    MonotoneOn (fun t => G.envelope h (x t)) (Icc a b) ∧
      (∀ᵐ t, t ∈ Icc a b → x t ∉ K → δ ≤ deriv (fun u => G.envelope h (x u)) t) := by
  classical
  let : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
  let f := fun j (t : ℝ) => dot (G.slope j) (x t) + G.offset j h
  have hf (j : Fin G.n) : AbsolutelyContinuousOnInterval (f j) a b := by
    have hl : LipschitzWith ‖dotCLM (G.slope j)‖₊
        (fun z : Fin d → ℝ => dot (G.slope j) z + G.offset j h) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simpa only [dist_add_right, dotCLM_apply] using
        (dotCLM (G.slope j)).lipschitzWith.dist_le_mul z w
    exact lipschitz_comp_ac hl hx
  have hcap (t : ℝ) : G.envelope h (x t) ≤ G.offset j0 h := by
    simpa [hz, dot] using G.envelope_le h (x t) j0
  have hbelow : ∀ᵐ t, t ∈ Icc a b → G.envelope h (x t) < G.offset j0 h →
      ∀ j ∈ (Finset.univ : Finset (Fin G.n)), G.envelope h (x t) = f j t →
        δ ≤ deriv (f j) t := by
    filter_upwards [hd] with t ht htmem hlt j _ he
    have hnot : x t ∉ K := by
      intro hk
      have heq := (G.plateau_eq_ceiling h hz hK (x t)).mp hk
      exact (ne_of_lt hlt) heq
    exact ht htmem hnot j ((G.envelope_eq_iff h (x t) j).mp he)
  have hdr := ae_capped_min_drift Finset.univ Finset.univ_nonempty f hab hδ
    (G.envelope_ac h hx) (fun j _ => hf j) hcap hbelow
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    have hsub : uIcc s t ⊆ uIcc a b := by
      rw [uIcc_of_le hst, uIcc_of_le hab]
      exact Icc_subset_Icc hs.1 ht.2
    have hd0 : ∀ᵐ u, u ∈ Icc s t → 0 ≤ deriv (fun v => G.envelope h (x v)) u := by
      filter_upwards [hdr] with u hu humem
      exact (hu ⟨hs.1.trans humem.1, humem.2.trans ht.2⟩).1
    have hi := ac_integrated_drift hst ((G.envelope_ac h hx).mono hsub) hd0
    simpa only [zero_mul, sub_nonneg] using hi
  · filter_upwards [hdr] with t ht htmem hnot
    apply (ht htmem).2
    exact lt_of_le_of_ne (hcap t)
      (fun he => hnot ((G.plateau_eq_ceiling h hz hK (x t)).mpr he))

/-- First-exit confinement applies to the AC envelope; this statement carries
the explicit remaining branch-drift obligation for the mass-action assembly. -/
theorem GeometricFamily.trapped_by_plateau (G : GeometricFamily d D) (h : ℝ)
    {j0 : Fin G.n} (hz : G.slope j0 = 0) {K B : Set (Fin d → ℝ)}
    (hK : ∀ x, x ∈ K ↔ AffineActive G.slope (fun j => G.offset j h) x j0)
    (hKB : K ⊆ interior B) (hB : IsClosed B)
    {x : ℝ → (Fin d → ℝ)} {T : ℝ} (hT : 0 ≤ T)
    (hx : AbsolutelyContinuousOnInterval x 0 T) (hx0 : x 0 ∈ K)
    (hd : ∀ τ ∈ Icc 0 T, MapsTo x (Icc 0 τ) B →
      ∀ᵐ t, t ∈ Icc 0 τ → x t ∉ K →
        ∀ j, AffineActive G.slope (fun k => G.offset k h) (x t) j →
          0 ≤ deriv (fun u => dot (G.slope j) (x u) + G.offset j h) t) :
    MapsTo x (Icc 0 T) K := by
  have hcap (z : Fin d → ℝ) : G.envelope h z ≤ G.offset j0 h := by
    simpa [hz, dot] using G.envelope_le h z j0
  have hF0 := (G.plateau_eq_ceiling h hz hK (x 0)).mp hx0
  have hbd (z : Fin d → ℝ) (hzB : z ∈ frontier B) : G.envelope h z ≠ G.offset j0 h := by
    intro he
    exact hzB.2 (hKB ((G.plateau_eq_ceiling h hz hK z).mpr he))
  have hmono (τ : ℝ) (hτ : τ ∈ Icc 0 T) (hseg : MapsTo x (Icc 0 τ) B) :
      MonotoneOn (G.envelope h ∘ x) (Icc 0 τ) := by
    have hs : uIcc 0 τ ⊆ uIcc 0 T := by
      rw [uIcc_of_le hτ.1, uIcc_of_le hT]
      exact Icc_subset_Icc_right hτ.2
    exact (G.envelope_monotone h hz hK hτ.1 le_rfl (hx.mono hs) (hd τ hτ hseg)).1
  have hh := Geometry.mapsTo_plateau_of_monotone_on_box hT hB
    (by simpa only [uIcc_of_le hT] using hx.continuousOn)
    (hKB hx0) hcap hF0 hbd hmono
  intro t ht
  exact (G.plateau_eq_ceiling h hz hK (x t)).mpr (hh ht).2

end EndotacticPermanence
