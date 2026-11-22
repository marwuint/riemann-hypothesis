import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NarrowLemmaOfCrystallineLubinTate
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConjugateNotMemFiltrationOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory.GalCut7.IwahoriTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut.SsTwist Polynomial UpperTheory.V UpperTheory.V.Af

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : Formalism.ConjugateSelfDual.IsPlaceOver A w}

theorem monodromy_vanishes_weilTwist_iff (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).mono0 ↔ x.mono0 := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff]
  rfl

theorem charPol_lpTwist_iff (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (y.lpTwist ξ hξ).charPol g ↔ x.charPol g = y.charPol g := by
  rw [charPol_lpTwist, charPol_lpTwist]
  exact ⟨scaleRoots_cancel (Units.ne_zero _), fun e => by rw [e]⟩

end GlobalTheory.GalCut7.IwahoriTwist

end
