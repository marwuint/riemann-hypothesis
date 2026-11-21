import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
