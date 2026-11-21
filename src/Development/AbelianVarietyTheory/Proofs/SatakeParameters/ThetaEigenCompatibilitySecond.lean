import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

