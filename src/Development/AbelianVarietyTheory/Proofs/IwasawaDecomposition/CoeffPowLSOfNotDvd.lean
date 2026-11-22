import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Subst

variable {R : Type} [CommRing R] {a : ℕ} (ha : 1 ≤ a)

variable {K : Type} [Field K]

end Subst

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

end GlobalTheory.LocM.FJ
