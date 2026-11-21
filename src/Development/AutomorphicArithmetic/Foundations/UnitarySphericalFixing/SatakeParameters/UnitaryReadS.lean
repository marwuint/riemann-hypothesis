import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSpeh
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSpehOfOfIsQuotOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import BuildAid.D4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import GroundTheory.PAdicHodge.AInfGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteGeneralOfOld
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertB

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC GlobalTheory.PRep

namespace UpperTheory.One.M.Ud

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def UnitaryReadS {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A) (rc : RecMap A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w → GlobalTheory.DefiniteBCGood.GoodSplitU U ∧
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BCSupport in

theorem good_of_sph {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (h1 : GlobalTheory.LGrp.IsSpherical (locProd h w σ) (GlobalTheory.LFun.KGL w n)) (i) :
    Good (clsOf (σ i)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
  have h1' : GlobalTheory.LGrp.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) (GlobalTheory.LFun.KGL w n) := isSpherical_of_equiv e h1
  have h3 : GlobalTheory.SmGL.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) :=
    isSphericalFor_of_eq (GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko w n) ((GlobalTheory.LGrp.isSpherical_iff _ _).1 h1')
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ _
    (GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ c n _ h _ _ (IsSubquotient.refl _) h3 i)).2

end UpperTheory.One.M.Ud

end
