import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.UnifLamFibre

open GlobalTheory.CechPic

theorem isSquare_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)

end GlobalTheory.UnifLamFibre
