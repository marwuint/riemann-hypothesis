import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.CoverInt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e}

instance measurableSpace (a : Fin (M.n + 1)) : MeasurableSpace (M.X a) := borel _

instance borelSpace (a : Fin (M.n + 1)) : BorelSpace (M.X a) := ⟨rfl⟩

def tChart (I : ManIs M Y) {a : Fin (M.n + 1)} (c : AlgChart Y.str (I.ε a) e) :
    OpenPartialHomeomorph (M.X a) (ReciprocityTheory.L2DbarEstimates.V e) :=
  (I.pt a).transOpenPartialHomeomorph c.e

end GlobalTheory.Mean4O.CoverInt
