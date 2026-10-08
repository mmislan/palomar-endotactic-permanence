module
public import proofs.EndotacticPermanence.CompactPermanence

@[expose] public section

/-! Forward-time null-set repair. The exceptional set is independent of the
state and of every candidate curve. This additive module preserves the saved
natural-complex theorem and its ambient uniqueness conclusion. -/

namespace EndotacticPermanence

open Set Filter MeasureTheory

noncomputable section

/-- Lebesgue measure restricted to the forward half-line. -/
def forwardVolume : Measure ℝ := volume.restrict (Ici 0)

/-- Rates are measurable and within the fixed positive box almost everywhere
on forward time; their negative-time values are unrestricted. -/
def AEAdmissible {R : Type*} (B : PositiveRateBox R) (k : ℝ → R → ℝ) : Prop :=
  (∀ e, AEMeasurable (fun t => k t e) forwardVolume) ∧
    ∀ᵐ t ∂forwardVolume, B.Contains (k t)

/-- A coordinatewise measurable representative clamped to the rate box.
There is one common exceptional set for the entire finite reaction family. -/
theorem repair_rate_history {R : Type*} [Fintype R]
    (B : PositiveRateBox R) (k : ℝ → R → ℝ) (hk : AEAdmissible B k) :
    ∃ kr : ℝ → R → ℝ,
      (∀ e, Measurable (fun t => kr t e)) ∧
      (∀ t, B.Contains (kr t)) ∧ k =ᵐ[forwardVolume] kr := by
  classical
  let g : ℝ → R → ℝ := fun t e => (hk.1 e).mk (fun u => k u e) t
  let kr : ℝ → R → ℝ := fun t e => max (B.lower e) (min (B.upper e) (g t e))
  have hgm (e : R) : Measurable (fun t => g t e) := (hk.1 e).measurable_mk
  have hge : ∀ᵐ t ∂forwardVolume, ∀ e, k t e = g t e :=
    ae_all_iff.mpr (fun e => (hk.1 e).ae_eq_mk)
  refine ⟨kr, ?_, ?_, ?_⟩
  · intro e
    exact measurable_const.max (measurable_const.min (hgm e))
  · intro t e
    exact ⟨le_max_left _ _, max_le (B.lower_le_upper e) (min_le_left _ _)⟩
  · filter_upwards [hge, hk.2] with t hgt hbt
    funext e
    dsimp [kr]
    rw [← hgt e, min_eq_right (hbt e).2, max_eq_right (hbt e).1]

/-- State-independent equality of the vector fields outside a common null set. -/
theorem indexed_mass_action_forward_ae_eq {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℕ) {k kr : ℝ → R → ℝ}
    (heq : k =ᵐ[forwardVolume] kr) :
    ∀ᵐ t ∂forwardVolume, ∀ x,
      indexedMassAction source target (k t) x =
        indexedMassAction source target (kr t) x := by
  filter_upwards [heq] with t ht
  intro x
  rw [ht]

/-- The AC/a.e.-ODE predicate depends only on the forward a.e. field class.
This equivalence applies to every competing curve, not only a constructed one. -/
theorem caratheodory_solution_congr_forward_ae {d : ℕ}
    {f g : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    (hfg : ∀ᵐ t ∂forwardVolume, ∀ x, f t x = g t x)
    {x0 : Fin d → ℝ} {x : ℝ → (Fin d → ℝ)} :
    IsCaratheodorySolution f x0 x ↔ IsCaratheodorySolution g x0 x := by
  have hfg' : ∀ᵐ t ∂volume, t ∈ Ici (0 : ℝ) → ∀ z, f t z = g t z :=
    ae_imp_of_ae_restrict hfg
  constructor
  · intro hx
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro T hT
    filter_upwards [hx.2.2 T hT, hfg'] with t ht he htmem
    have hd := ht htmem
    rwa [he htmem.1.le (x t)] at hd
  · intro hx
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro T hT
    filter_upwards [hx.2.2 T hT, hfg'] with t ht he htmem
    have hd := ht htmem
    rwa [← he htmem.1.le (x t)] at hd

/-- Compact-initial uniform permanence for natural complexes with a.e.
admissible histories. K precedes Q and k; T(Q) precedes x0 and k. -/
theorem endotactic_permanence_compact_ae {d : ℕ} {R : Type*} [Fintype R]
    (source target : R → Fin d → ℕ)
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
              IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 y →
                EqOn x y (Ici 0))) ∧
      (∀ x0 ∈ K, ∀ k : ℝ → R → ℝ, AEAdmissible B k →
        ∀ x : ℝ → (Fin d → ℝ),
          IsCaratheodorySolution (fun t => indexedMassAction source target (k t)) x0 x →
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
    exact ⟨x, (hsol x).mpr hx, hxclass, hxK, fun y hy => huniq y ((hsol y).mp hy)⟩
  · intro x0 hx0 k hk x hx t ht
    obtain ⟨kr, hkrm, hkrb, heq⟩ := repair_rate_history B k hk
    exact hinv x0 hx0 kr hkrm (fun u _ => hkrb u) x
      ((caratheodory_solution_congr_forward_ae
        (indexed_mass_action_forward_ae_eq source target heq)).mp hx) t ht

end

end EndotacticPermanence
