import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftInjNonVanTypeNZOfPrints

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory
theorem DownLift.nonvanishing_of_down_lift : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  intro h1 h2 h4 h5 h6 D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t
  exact ((_root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given h1 h2 h4 h5 h6 D G Pl0 T A Ks R F hG hF).2 i t).1
end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGalois_downLift_nonvanishing : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  first | exact @_root_.GlobalTheory.DownLift.nonvanishing_of_down_lift | exact _root_.GlobalTheory.DownLift.nonvanishing_of_down_lift | (intros; apply _root_.GlobalTheory.DownLift.nonvanishing_of_down_lift <;> assumption)
end
