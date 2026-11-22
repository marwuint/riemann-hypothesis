import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EulerFactorFromDoubling

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory.Core.Rk.LiftOnto
theorem liftInj_nonVan_typeNZ_of_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL →
    GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram →
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
      [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  intro hDec hDbl hGL hHecke hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull
  have hEul : GlobalTheory.Core.Rk.IP.EulerRight D := _root_.GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling hDec hGL D
  have hPole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole := GlobalTheory.LiftPoleObj.simplePole_of_hecke hHecke
  have hNe : DownNe D := _root_.GlobalTheory.T.downNe_of_eulerRight_doubling hDbl hPole D hEul
  have hNV : ∀ i t, NonVan R i t := _root_.GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe D hNe G Pl0 T A Ks R F hG hFull
  have hEig : ∀ i t, DownEig R i t := _root_.GlobalTheory.DownEigen.downEig hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := _root_.GlobalTheory.DownLift.GenFinite.genFin hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := _root_.GlobalTheory.GenReal.genInf D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := _root_.GlobalTheory.GoodLift.goodMem_of_given D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := _root_.GlobalTheory.GoodTypeNoChi.goodNoChi D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := _root_.GlobalTheory.UnrAll.unrCorr_all hDec hHowe D G Pl0 T A Ks R F hG hFull
  have hOk : ∀ i t (ok : Pl D.host.E → Prop), UnrCorr R i t ok := by
    intro i t ok h hh s c y hy h1 h2 B B' hB hB' w hw _
    exact hU i t h hh s c y hy h1 h2 B B' hB hB' w hw trivial
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  exact ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hOk i A.μ0 _, hOk i A.μ0 _, hPar i A.μ0⟩),
    fun i t => ⟨hNV i t, hTNZ i t⟩⟩
end GlobalTheory.Core.Rk.LiftOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  first | exact @_root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | exact _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt <;> assumption)
end
