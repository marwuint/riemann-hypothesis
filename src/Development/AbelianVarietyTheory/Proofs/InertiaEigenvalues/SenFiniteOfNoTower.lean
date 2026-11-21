import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongrFiltrationDetectingCharactersCoboundary

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.PMon.Ram

theorem senFinite_of_noTower (hNT : NoTower) : SenFinite := by
  intro l _ n _ _ K ρ hc M hM
  obtain ⟨N, hN, hanti, hopen, hpow, hroot, hker⟩ := _root_.GlobalTheory.congrFiltration l n K ρ hc
  have hdet := _root_.GlobalTheory.congrFiltration_detectingCharacters_coboundary l n K ρ M hM N hN
  obtain ⟨k, hk⟩ := hNT l K N hanti hopen hpow hroot hdet
  refine _root_.GlobalTheory.GK.finite_image_of_trivial_on_open l K (GL n ℚ_[l]) ρ (IK K) (N k) (hopen k) ?_
  intro g hgI hgN
  exact hker g (fun j => hk j ⟨hgI, hgN⟩)

end GlobalTheory.PMon.Ram
