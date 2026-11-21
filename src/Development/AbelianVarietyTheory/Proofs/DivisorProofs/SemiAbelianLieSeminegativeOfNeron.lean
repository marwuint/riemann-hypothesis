import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromPullbackPiMapStalkLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
