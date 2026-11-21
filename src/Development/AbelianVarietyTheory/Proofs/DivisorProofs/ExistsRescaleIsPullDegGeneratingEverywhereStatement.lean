import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  first | exact @GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | exact GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | (intros; apply GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top <;> assumption)
