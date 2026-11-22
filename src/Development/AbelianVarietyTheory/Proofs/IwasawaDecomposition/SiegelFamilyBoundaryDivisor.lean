import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegChart

theorem isAdmissibleBase_of_completeNormalLocalCharZero {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : IsCN A) : LN.admitted A (maximalIdeal A) :=
  ⟨admissibleBase_of_completeNormalLocalCharZero hA, hA.2.2.1, hA.2.2.2, inferInstance, inferInstanceAs (IsIntegrallyClosed (ResidueField A))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.SiegChart
