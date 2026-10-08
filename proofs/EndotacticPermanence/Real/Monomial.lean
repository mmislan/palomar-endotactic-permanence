module
public import proofs.EndotacticPermanence.Imported.MonomialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw

@[expose] public section

namespace EndotacticPermanence.RealComplex

open OAI.Problem326 Set
open scoped BigOperators

noncomputable section

/-- Positive-domain monomial for arbitrary real exponent vectors.
Only its values at strictly positive states are used by the network theorem. -/
def monomial {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  Real.exp (∑ i, y i * Real.log (x i))

theorem monomial_pos {d : ℕ} (x y : Fin d → ℝ) : 0 < monomial x y :=
  Real.exp_pos _

theorem monomial_eq_prod_rpow {d : ℕ} {x : Fin d → ℝ}
    (hx : PositiveState x) (y : Fin d → ℝ) :
    monomial x y = ∏ i, (x i) ^ (y i) := by
  unfold monomial
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (hx i)]
  congr 1
  ring

/-- Natural monomials agree on the positive orthant, without a boundary claim. -/
theorem monomial_nat_agreement {d : ℕ} {x : Fin d → ℝ}
    (hx : PositiveState x) (y : Fin d → ℕ) :
    monomial x (fun i => (y i : ℝ)) = OAI.Problem326.monomial x y := by
  rw [monomial_eq_prod_rpow hx]
  simp only [Real.rpow_natCast, OAI.Problem326.monomial]

theorem monomial_rpow {d : ℕ} {h : ℝ} (hh : 0 < h)
    (p y : Fin d → ℝ) :
    monomial (fun i => h ^ p i) y = h ^ (∑ i, p i * y i) := by
  unfold monomial
  rw [Real.rpow_def_of_pos hh]
  congr 1
  simp_rw [Real.log_rpow hh]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem monomial_le_rpow_mul_of_gap {d : ℕ} {h H : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (p y z : Fin d → ℝ)
    (hgap : H ≤ ∑ i, p i * (z i - y i)) :
    monomial (fun i => h ^ p i) z ≤ h ^ H * monomial (fun i => h ^ p i) y := by
  rw [monomial_rpow hh, monomial_rpow hh, ← Real.rpow_add hh]
  apply Real.rpow_le_rpow_of_exponent_ge hh hh1
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib] at hgap
  linarith

end
end EndotacticPermanence.RealComplex
