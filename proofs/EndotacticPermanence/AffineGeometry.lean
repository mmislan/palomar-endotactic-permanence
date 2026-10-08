module
public import proofs.EndotacticPermanence.Imported.AffineExistence
public import proofs.EndotacticPermanence.Imported.AffineUniformCertificate
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace EndotacticPermanence

open OAI.Problem326.Affine

/-- Exact graph-independent imported geometry, retaining the slope cube in C. -/
theorem affine_geometry (d : ℕ) (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, 0 < E r) :
    ∃ C : FullCertificate d (-1) 1 E,
      ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
        ∀ p : Fin d → ℝ, Cube (-1) 1 p → ∀ L ∈ C.labels,
          Active C.labels L h (powerPoint h p) → ‖p - L.slope‖ < E L.slope := by
  obtain ⟨C⟩ := exists_fullCertificate d (-1) 1 E (by norm_num) (fun r _ => hE r)
  obtain ⟨h0, hh0, hu⟩ := C.uniform_activity
  exact ⟨C, h0, hh0, hu⟩

end EndotacticPermanence
