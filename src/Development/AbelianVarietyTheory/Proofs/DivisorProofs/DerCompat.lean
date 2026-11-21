import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToOverSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankLineHyperplane
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSAgree

theorem dual_alg {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (dualMap r).comp (algebraMap S (DualNumber S)) = (algebraMap S' (DualNumber S')).comp r := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

theorem fst_dual {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap r) = r.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext a <;> (try simp [dualMap]) <;> rfl

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem eps_over {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') :
    spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x' := by
  rw [← hx, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', dual_alg]

theorem tan_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t x' (spMap (dualMap r) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, eps_over r hx]
  · have h : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap r) =
        spMap r ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', fst_dual]
    rw [← Category.assoc, h, Category.assoc, hv.2]
    let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap r) hx
    exact congrArg CommaMorphism.left (comp_one k (M := t.G))

end Gen

theorem tan_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsTanAtG t (chart U) v → IsTanAtG t (chart W) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v) :=
  fun _ _ _ _ _ _ t U W hW _ hv => tan_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) hv

end GlobalTheory.KSAgree
