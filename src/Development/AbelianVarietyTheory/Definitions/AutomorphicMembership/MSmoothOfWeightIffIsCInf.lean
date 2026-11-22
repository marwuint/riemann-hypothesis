import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CxStage

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

end GlobalTheory.TrueGeo
