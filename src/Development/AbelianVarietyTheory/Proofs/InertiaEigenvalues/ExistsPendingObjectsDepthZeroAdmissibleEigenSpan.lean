import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSectionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.PendClose

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) →
    SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D →
    SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  intro D M hT hR hA hPar h0 h5 hIne hDep hGen hZL hCI hCT hSer hZeta hDZ hAdm
  have hSU : GlobalTheory.EtaJoin.SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hSec : ∀ i, Nonempty (Sec D i) := fun i =>
    _root_.GlobalTheory.PendOf.SecProof.main D M i hT hR hA hSU (_root_.GlobalTheory.HeckeScalarAll.heckeScalar_all D M hT hA i)
  obtain ⟨lz, hlz⟩ := _root_.GlobalTheory.LzExist.exists_lz_serEq D
  obtain ⟨Ω, hΩ⟩ := _root_.GlobalTheory.PendOf.LabIneAll.main D hIne hDep hGen
  have hChar : LabChar D := _root_.main D h0 hIne hDep hGen
  obtain ⟨Z⟩ := _root_.GlobalTheory.CenOAct.cenO_nonempty D hSec hZL hCI hCT
  have hPr : PrType D := _root_.GlobalTheory.PendOf.PrTypeProof.main D hSec
  have hSplit : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := fun k v =>
    _root_.GlobalTheory.TypeSplit.main D k _ (D.naut.plGw_over k v)
  have hPS : ParSurj D := _root_.GlobalTheory.ParOfPoint.main D hPar h0 h5 hSplit hDep hDZ
  let P : PairedCharacterCondition.Pend D := mk lz hlz hSer hZeta Ω hΩ hChar Z hZL hPr hPS
  exact ⟨P, GlobalTheory.T.depthZeroAdmissible_all_pending_data D P hAdm, GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections D P hSec hCT⟩

end GlobalTheory.PendClose
