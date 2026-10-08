module
public import proofs.EndotacticPermanence.Real.CompactPermanence
public import proofs.EndotacticPermanence.AlmostEverywhereRates

@[expose] public section

namespace EndotacticPermanence.RealComplex
open Set Filter MeasureTheory
noncomputable section

theorem indexed_mass_action_forward_ae_eq {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℝ) {k kr : ℝ → R → ℝ}
    (heq : k =ᵐ[forwardVolume] kr) :
    ∀ᵐ t ∂forwardVolume, ∀ x,
      indexedMassAction source target (k t) x =
        indexedMassAction source target (kr t) x := by
  filter_upwards [heq] with t ht
  intro x
  rw [ht]

/-- Compact-initial uniform permanence for real complexes with a.e.
admissible histories. K precedes Q and k; T(Q) precedes x0 and k. -/
theorem endotactic_permanence_compact_ae {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℝ)
    (endo : Endotactic source target) (B : PositiveRateBox R)
    (c : Fin d → ℝ) (hc : OAI.Problem326.PositiveState c) :
    ∃ K : Set (Fin d → ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      K ⊆ positiveClass source target c ∧
      (∀ Q : Set (Fin d → ℝ), IsCompact Q → Q ⊆ positiveClass source target c →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ x0 ∈ Q, ∀ k : ℝ → R → ℝ,
          AEAdmissible B k → ∃ x : ℝ → (Fin d → ℝ),
            IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x ∧
            (∀ t : ℝ, 0 ≤ t → x t ∈ positiveClass source target c) ∧
            (∀ t : ℝ, T ≤ t → x t ∈ K) ∧
            (∀ y : ℝ → (Fin d → ℝ),
              IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 y → (∀ t : ℝ, 0 ≤ t → OAI.Problem326.PositiveState (y t)) →
                EqOn x y (Ici 0))) ∧
      (∀ x0 ∈ K, ∀ k : ℝ → R → ℝ, AEAdmissible B k →
        ∀ x : ℝ → (Fin d → ℝ),
          IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x → (∀ t : ℝ, 0 ≤ t → OAI.Problem326.PositiveState (x t)) →
          ∀ t : ℝ, 0 ≤ t → x t ∈ K) := by
  obtain ⟨K, hne, hcompact, hconvex, hsub, habs, hinv⟩ :=
    endotactic_permanence_compact source target endo B c hc
  refine ⟨K, hne, hcompact, hconvex, hsub, ?_, ?_⟩
  · intro Q hQ hQsub
    obtain ⟨T, hT, hentry⟩ := habs Q hQ hQsub
    refine ⟨T, hT, ?_⟩
    intro x0 hx0 k hk
    obtain ⟨kr, hkrm, hkrb, heq⟩ := repair_rate_history B k hk
    have hsol (z : ℝ → (Fin d → ℝ)) :
        IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 z ↔
          IsCaratheodorySolution (fun t => indexedMassAction source target (kr t)) x0 z :=
      caratheodory_solution_congr_forward_ae
        (indexed_mass_action_forward_ae_eq source target heq)
    obtain ⟨x, hx, hxclass, hxK, huniq⟩ :=
      hentry x0 hx0 kr hkrm (fun t _ => hkrb t)
    exact ⟨x, (hsol x).mpr hx, hxclass, hxK, fun y hy hypos => huniq y ((hsol y).mp hy) hypos⟩
  · intro x0 hx0 k hk x hx hxpos t ht
    obtain ⟨kr, hkrm, hkrb, heq⟩ := repair_rate_history B k hk
    exact hinv x0 hx0 kr hkrm (fun u _ => hkrb u) x
      ((caratheodory_solution_congr_forward_ae
        (indexed_mass_action_forward_ae_eq source target heq)).mp hx) hxpos t ht

end
end EndotacticPermanence.RealComplex
