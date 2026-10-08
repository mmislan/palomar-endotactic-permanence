module
public import proofs.EndotacticPermanence.GeometricFamily
public import proofs.EndotacticPermanence.CappedMinimumAC

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326 Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable def dotCLM {d : ℕ} (r : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, r i • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)

theorem dotCLM_apply {d : ℕ} (r x : Fin d → ℝ) : dotCLM r x = dot r x := by
  simp [dotCLM, dot]

variable {d : ℕ} {D : Finset (Fin d → ℝ)}

noncomputable def GeometricFamily.envelope (G : GeometricFamily d D) (h : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  haveI : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
  Finset.univ.inf' Finset.univ_nonempty (fun j => dot (G.slope j) x + G.offset j h)

theorem GeometricFamily.envelope_le (G : GeometricFamily d D) (h : ℝ)
    (x : Fin d → ℝ) (j : Fin G.n) :
    G.envelope h x ≤ dot (G.slope j) x + G.offset j h :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem GeometricFamily.envelope_eq_iff (G : GeometricFamily d D) (h : ℝ)
    (x : Fin d → ℝ) (j : Fin G.n) :
    G.envelope h x = dot (G.slope j) x + G.offset j h ↔
      AffineActive G.slope (fun k => G.offset k h) x j := by
  constructor
  · intro he k
    rw [← he]
    exact G.envelope_le h x k
  · intro ha
    let : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
    apply le_antisymm (G.envelope_le h x j)
    exact Finset.le_inf' Finset.univ_nonempty _ (fun k _ => ha k)

theorem GeometricFamily.envelope_ac (G : GeometricFamily d D) (h : ℝ)
    {x : ℝ → (Fin d → ℝ)} {a b : ℝ} (hx : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun t => G.envelope h (x t)) a b := by
  classical
  let : Nonempty (Fin G.n) := Fin.pos_iff_nonempty.mp G.n_pos
  let L : NNReal := ∑ j, ‖dotCLM (G.slope j)‖₊
  have hf (j : Fin G.n) : LipschitzWith L
      (fun x : Fin d → ℝ => dot (G.slope j) x + G.offset j h) := by
    have hj : LipschitzWith ‖dotCLM (G.slope j)‖₊
        (fun x => dotCLM (G.slope j) x + G.offset j h) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_add_right] using (dotCLM (G.slope j)).lipschitzWith.dist_le_mul x y
    have hle : ‖dotCLM (G.slope j)‖₊ ≤ L := by
      exact Finset.single_le_sum (f := fun k => ‖dotCLM (G.slope k)‖₊)
        (fun _ _ => zero_le) (Finset.mem_univ j)
    simpa only [dotCLM_apply] using hj.weaken hle
  exact lipschitz_comp_ac
    (lipschitz_finset_min L _ Finset.univ Finset.univ_nonempty (fun j _ => hf j)) hx

theorem affine_branch_hasDerivAt {d : ℕ} (r : Fin d → ℝ) (b : ℝ)
    {x : ℝ → (Fin d → ℝ)} {v : Fin d → ℝ} {t : ℝ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun u => dot r (x u) + b) (dot r v) t := by
  simpa only [Function.comp_def, dotCLM_apply] using
    ((dotCLM r).hasFDerivAt.comp_hasDerivAt t hx).add_const b

end EndotacticPermanence
