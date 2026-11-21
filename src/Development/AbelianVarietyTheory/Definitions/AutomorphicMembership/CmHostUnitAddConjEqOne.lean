import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueTransUnit
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

namespace GlobalTheory.LocM

namespace Bdy

namespace BDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t₀ : SAB H X} {x : X} (B : BDat t₀ x)

abbrev Ylat : Type := B.U.D.toPre.X

def chX : Type := B.Ylat
instance : AddCommGroup B.chX := inferInstanceAs (AddCommGroup B.Ylat)
instance : Module (𝓞 E) B.chX := Module.compHom B.Ylat (H.bar : 𝓞 E →+* 𝓞 E)

instance : GeometricallyConnected B.t.G.hom := B.t.semi.geomConnected

end BDat

end Bdy

open Bdy

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

end At

end GlobalTheory.LocM
