import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecPrOfZSpecTypeTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (_root_.GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum D M AV i (CS i)) (TC i) II PZ
      (_root_.GlobalTheory.ExhaustRows.main D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := _root_.GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds D M i HT HR AV SU (_root_.GlobalTheory.HeckeScalarAll.heckeScalar_all D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
