import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
set_option maxHeartbeats 4000000 in
theorem locW_of_nTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    ∀ i σ w, D'.naut.locW i σ w = Rw.locR σ w := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  intro i σ w
  rw [e1]
  exact Au.locW i σ w
end GlobalTheory.GalLoc.RowParamAt
end
