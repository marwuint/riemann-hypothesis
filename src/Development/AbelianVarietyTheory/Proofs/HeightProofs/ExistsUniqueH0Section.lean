import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange

noncomputable section

namespace GlobalTheory.ArcCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints hiding Wit WitBC
open GlobalTheory.ConstTan GlobalTheory.FormalPoint ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj MonObj

section Gt

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem comb_iff {m : ℕ} (cf : Fin m → A) (e : Fin m → Out.GtPt D₀ (epsR A)) (ν : Out.GtPt D₀ (epsR A)) :
    GtComb cf e ν ↔ IsCombGt e cf ν := Iff.rfl

variable {A' : Type} [CommRing A'] [IsDomain A'] {D₁ : Out.DegPre A'} {f : A →+* A'}

end Gt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.ArcCompare
