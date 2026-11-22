import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankLineHyperplane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open scoped NNReal
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.KernelNoTorsion GlobalTheory.TangentPow
open GlobalTheory.GmPoints GlobalTheory.HodgeTateImage GlobalTheory.CompHt.FormalChar

namespace GlobalTheory.TorsCharDlog

section Transfer

variable {X : Scheme.{0}} {O : Type} [CommRing O] {z : Sp O ⟶ X} {G : Over (Sp O)} [GrpObj G]
  {G' : Over X} [GrpObj G'] {φ : G.left ⟶ G'.left} (hφ : IsGrpPullback G G' z φ)

variable (R : Type) [CommRing R] [Algebra O R]

end Transfer

end GlobalTheory.TorsCharDlog

namespace GlobalTheory.TorsCharDlog

end GlobalTheory.TorsCharDlog
