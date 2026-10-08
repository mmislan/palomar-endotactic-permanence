module
public import proofs.EndotacticPermanence.EndotacticWitness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace EndotacticPermanence

open scoped BigOperators

/-- Projection-weighted drift. The ratio assumptions are supplied by active
source separation; the rate inequalities come from the declared box. -/
theorem rate_box_drift {R : Type*} [Fintype R]
    (a m lower upper k : R → ℝ) (j : R) (q : ℝ)
    (hm : ∀ e, 0 < m e) (hlower : ∀ e, 0 < lower e)
    (hk : ∀ e, lower e ≤ k e ∧ k e ≤ upper e)
    (hj : 0 < a j)
    (hratio : ∀ e, a e < 0 → m e ≤ q * m j) :
    m j * (lower j * a j - q *
      ∑ e : R, if a e < 0 then upper e * |a e| else 0) ≤
      ∑ e : R, k e * m e * a e := by
  classical
  let cost : R → ℝ := fun e => if a e < 0 then upper e * |a e| else 0
  have hpoint : ∀ e : R,
      (if e = j then lower j * m j * a j else 0) - q * m j * cost e ≤
        k e * m e * a e := by
    intro e
    by_cases heq : e = j
    · subst e
      have hn : ¬ a j < 0 := not_lt_of_ge hj.le
      simp only [cost, ite_eq_right hn, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hk j).1 (hm j).le) hj.le
    · simp only [ite_eq_right heq]
      by_cases ha : a e < 0
      · simp only [cost, ite_eq_left ha, zero_sub]
        have hu : 0 ≤ upper e := (hlower e).le.trans ((hk e).1.trans (hk e).2)
        calc
          -(q * m j * (upper e * |a e|)) = upper e * (q * m j) * a e := by
            rw [abs_of_neg ha]
            ring
          _ ≤ upper e * m e * a e :=
            mul_le_mul_of_nonpos_right
              (mul_le_mul_of_nonneg_left (hratio e ha) hu) ha.le
          _ ≤ k e * m e * a e :=
            mul_le_mul_of_nonpos_right
              (mul_le_mul_of_nonneg_right (hk e).2 (hm e).le) ha.le
      · simp only [cost, ite_eq_right ha, mul_zero, sub_zero]
        exact mul_nonneg
          (mul_nonneg ((hlower e).le.trans (hk e).1) (hm e).le)
          (le_of_not_gt ha)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  have heval : (∑ e : R,
      ((if e = j then lower j * m j * a j else 0) - q * m j * cost e)) =
      m j * (lower j * a j - q * ∑ e : R, cost e) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ← Finset.mul_sum]
    simp only [Finset.mem_univ, ite_true]
    ring
  rw [heval] at hs
  simpa only [cost] using hs

theorem rate_box_half_margin {R : Type*} [Fintype R]
    (a m lower upper k : R → ℝ) (j : R) (q : ℝ)
    (hm : ∀ e, 0 < m e) (hlower : ∀ e, 0 < lower e)
    (hk : ∀ e, lower e ≤ k e ∧ k e ≤ upper e)
    (hj : 0 < a j)
    (hratio : ∀ e, a e < 0 → m e ≤ q * m j)
    (hsmall : q * (∑ e : R, if a e < 0 then upper e * |a e| else 0) ≤
      lower j * a j / 2) :
    0 < ∑ e : R, k e * m e * a e := by
  have h := rate_box_drift a m lower upper k j q hm hlower hk hj hratio
  have hpos : 0 < lower j * a j := mul_pos (hlower j) hj
  have hbracket : 0 < lower j * a j - q *
      (∑ e : R, if a e < 0 then upper e * |a e| else 0) := by linarith
  exact (mul_pos (hm j) hbracket).trans_le h

end EndotacticPermanence
