import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricFunctionInverseInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetRowOfGaloisRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtString

open GlobalTheory.SphPar GlobalTheory.SphGal GlobalTheory.Hk3 GlobalTheory.CuspRep Formalism.UG Polynomial
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {D : D7}

theorem isSplit_iff_conj (P : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  rw [GlobalTheory.LFun.isSplit_iff, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · rintro ⟨w, w', hne, h, h'⟩ e
    have e' : Formalism.DivisionValues.conjPl P = P := HeightOneSpectrum.ext e
    have a := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have b := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h'
    rw [e', or_self] at a b
    exact hne (a.trans b.symm)
  · intro h
    exact ⟨P, Formalism.DivisionValues.conjPl P, fun e => h (congrArg HeightOneSpectrum.asIdeal e).symm, rfl,
      (GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)).symm⟩

end GlobalTheory.PtString

end
