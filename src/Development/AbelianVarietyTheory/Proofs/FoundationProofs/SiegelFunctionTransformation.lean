import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndTStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => _root_.GlobalTheory.Sieg.admissible_act_SL2 c x γ h)
    (fun x τ h => _root_.GlobalTheory.Sieg.sg_S c x τ h) (fun x τ _ => _root_.GlobalTheory.Sieg.sg_T_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
