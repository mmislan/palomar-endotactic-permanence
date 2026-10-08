module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Uniform permanence of endotactic reaction networks with measurable rates

Complexes may have arbitrary signed real coordinates. The ODE and uniqueness
are stated on the positive orthant. Histories are measurable and satisfy the
fixed positive rate bounds almost everywhere on forward time. The absorbing
set precedes the initial compact set and history; the entry time precedes the
initial state and history. All solution predicates below use only initial
data, local absolute continuity and the almost-everywhere ODE.

This is an independent statement. Deliberate Challenge proof holes are
permitted by Palomar; the corresponding Solution must have complete proofs.
-/

@[expose] public section
namespace EndotacticSubmission
open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section

/-- Strict positivity of every species concentration. -/
def Positive {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ i, 0 < x i

/-- The usual coordinate dot product. -/
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ i, u i * v i

/-- The reaction displacement, target minus source. -/
def displacement {d : ℕ} {R : Type*} (s t : R → Fin d → ℝ) (e : R) := t e - s e

/-- The real-exponent monomial, evaluated on positive states in the theorem. -/
def monomial {d : ℕ} (x y : Fin d → ℝ) : ℝ := Real.exp (∑ i, y i * Real.log (x i))

/-- Generalized mass action: the sum of rate times monomial times displacement. -/
def field {d : ℕ} {R : Type*} [Fintype R] (s t : R → Fin d → ℝ)
    (k : R → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  ∑ e, (k e * monomial x (s e)) • displacement s t e

/-- Ordinary endotacticity, tested in every real direction. Every adverse
reaction has an earlier source with strictly positive displacement projection. -/
def Endotactic {d : ℕ} {R : Type*} (s t : R → Fin d → ℝ) : Prop :=
  ∀ r : Fin d → ℝ, ∀ e, dot r (displacement s t e) < 0 →
    ∃ j, 0 < dot r (displacement s t j) ∧ dot r (s j) < dot r (s e)

/-- The real linear span of the reaction displacements. -/
def stoichiometricSpace {d : ℕ} {R : Type*} (s t : R → Fin d → ℝ) :
    Submodule ℝ (Fin d → ℝ) := Submodule.span ℝ (Set.range (displacement s t))

/-- The positive part of the affine stoichiometric class through c. -/
def positiveClass {d : ℕ} {R : Type*} (s t : R → Fin d → ℝ)
    (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | Positive x ∧ x - c ∈ stoichiometricSpace s t}

/-- Fixed coordinatewise lower and upper rate bounds with positive lower bound. -/
structure RateBox (R : Type*) where
  lower : R → ℝ
  upper : R → ℝ
  lower_pos : ∀ e, 0 < lower e
  lower_le_upper : ∀ e, lower e ≤ upper e

/-- Membership in the closed rate box. -/
def RateBox.Contains {R : Type*} (B : RateBox R) (k : R → ℝ) : Prop :=
  ∀ e, B.lower e ≤ k e ∧ k e ≤ B.upper e

/-- Coordinatewise a.e. measurability and a common a.e. bound on forward time.
No hypothesis is imposed on negative-time values. -/
def Admissible {R : Type*} (B : RateBox R) (k : ℝ → R → ℝ) : Prop :=
  (∀ e, AEMeasurable (fun u => k u e) (volume.restrict (Ici (0 : ℝ)))) ∧
    ∀ᵐ u ∂(volume.restrict (Ici (0 : ℝ))), B.Contains (k u)

/-- A forward Carathéodory solution: initial data, local absolute continuity,
and the vector ODE almost everywhere on each finite forward interval. -/
def Solution {d : ℕ} (f : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (x0 : Fin d → ℝ) (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval x 0 T) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ᵐ u, u ∈ Ioo 0 T → HasDerivAt x (f u (x u)) u)

/-- One compact convex forward-invariant absorbing set per positive class,
with entry time uniform over each compact initial set and all admissible
histories. Solutions exist globally and are unique among positive solutions. -/
theorem uniform_permanence {d : ℕ} {R : Type*} [Fintype R]
    (s t : R → Fin d → ℝ) (endo : Endotactic s t) (B : RateBox R)
    (c : Fin d → ℝ) (hc : Positive c) :
    ∃ K : Set (Fin d → ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      K ⊆ positiveClass s t c ∧
      (∀ Q : Set (Fin d → ℝ), IsCompact Q → Q ⊆ positiveClass s t c →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ x0 ∈ Q, ∀ k : ℝ → R → ℝ,
          Admissible B k → ∃ x : ℝ → (Fin d → ℝ),
            Solution (fun u => field s t (k u)) x0 x ∧
            (∀ u : ℝ, 0 ≤ u → x u ∈ positiveClass s t c) ∧
            (∀ u : ℝ, T ≤ u → x u ∈ K) ∧
            (∀ y : ℝ → (Fin d → ℝ),
              Solution (fun u => field s t (k u)) x0 y →
                (∀ u : ℝ, 0 ≤ u → Positive (y u)) → EqOn x y (Ici 0))) ∧
      (∀ x0 ∈ K, ∀ k : ℝ → R → ℝ, Admissible B k →
        ∀ x : ℝ → (Fin d → ℝ),
          Solution (fun u => field s t (k u)) x0 x →
            (∀ u : ℝ, 0 ≤ u → Positive (x u)) →
              ∀ u : ℝ, 0 ≤ u → x u ∈ K) := by
  sorry

/-- Initial-data stability in a fixed compact positive region for a common
admissible history. The constant is selected before the history and curves. -/
theorem continuous_dependence {d : ℕ} {R : Type*} [Fintype R]
    (s t : R → Fin d → ℝ) (B : RateBox R)
    (C : Set (Fin d → ℝ)) (hC : IsCompact C) (hpos : ∀ x ∈ C, Positive x) :
    ∃ L : NNReal, 0 ≤ (L : ℝ) ∧ ∀ k : ℝ → R → ℝ,
      Admissible B k → ∀ x0 y0 x y,
        Solution (fun u => field s t (k u)) x0 x →
        Solution (fun u => field s t (k u)) y0 y →
        (∀ u, 0 ≤ u → x u ∈ C) → (∀ u, 0 ≤ u → y u ∈ C) →
        ∀ u, 0 ≤ u → dist (x u) (y u) ≤ dist x0 y0 * Real.exp ((L : ℝ) * u) := by
  sorry

end
end EndotacticSubmission
