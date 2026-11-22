import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOfIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianLocusEqTrivialTorusLocusProper
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelCoordinatesLocalBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsHasGeoExistsClos
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharEqZeroOfIsProper
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyOfFourPropertiesGroupScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.GeoHalf.zhGeo : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → Laws3 → Laws4 → Laws5 → UTorsSt → ZHGeoSt :=
  GlobalTheory.ZH.GeoHalf.zhGeo_of @_root_.GlobalTheory.ZH.hasTests_of_real @_root_.GlobalTheory.ClosureGroup.exists_pre @_root_.GlobalTheory.ZH.AbelianPart.ab @_root_.GlobalTheory.ZH.SecCoord.secO @_root_.GlobalTheory.UnifNormal.exists_unif_psiUnitOn @GlobalTheory.ZH.baseFacts_hasGeo_exists_clos @GlobalTheory.ZH.ThetaData.exists_theta @GlobalTheory.ZH.TorsionValue.torsSec @GlobalTheory.ZH.TorsionSection.exists_section @_root_.GlobalTheory.ZH.IndepFib.indep_on_closed_fibre @GlobalTheory.ZH.AbelianLocus.abelian_locus @_root_.GlobalTheory.ZH.ZHPre.nonempty_out
