import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev PrimIso (t : SAB H X₀) : Type :=
  LB.Iso t.PP.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] t.PP.L)

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames
