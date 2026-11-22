import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.WeightExist

theorem weightEx : PositivityTheory.Rg.BcB.F.WeightEx :=
  fun E _ _ _ n π hπ τ => (_root_.GlobalTheory.DefU.AU.existsUnique_hasWt E n (GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.CompanionTheory.WeightExist
