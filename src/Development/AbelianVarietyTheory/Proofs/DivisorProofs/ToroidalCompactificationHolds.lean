import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersections
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso

namespace GlobalTheory

open NumberField

theorem toroidalCompactification_holds : GlobalTheory.Published.ToroidalCompactification := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φs, hs, -⟩ := _root_.GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt (max 1 (Module.finrank ℚ E * min Dw.p Dw.q))
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y, -, -, -, -, -, a₁, a₂, a₃, -⟩ := GlobalTheory.Published.ToroidalForFanKS.exists_model_of_fan _root_.GlobalTheory.TorKSField.toroidalForFanKS hr h₁ h₂ Xo c
  exact ⟨Y, a₁, a₂, a₃⟩

end GlobalTheory
