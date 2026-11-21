import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Mathlib
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

open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilTorsChar

theorem exists_mulEquiv_points {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let I : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
  refine ⟨⟨⟨F, I, fun x => ?_, fun y => ?_⟩, fun x y => ?_⟩, fun _ => rfl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
  · apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  · apply Over.OverMorphism.ext
    exact (h.2 T x y (F x) (F y) rfl rfl).symm

end GlobalTheory.WeilTorsChar
