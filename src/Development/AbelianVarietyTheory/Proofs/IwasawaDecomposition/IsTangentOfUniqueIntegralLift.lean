import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.LatPush

open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (mu : SABMap t' t f)

theorem exists_ptEquiv {T : Scheme.{0}} (q : T ⟶ X') (q' : T ⟶ X) (h : q ≫ f = q') :
    ∃ e : (Over.mk q ⟶ t'.G) ≃* (Over.mk q' ⟶ t.G), ∀ g, (e g).left = g.left ≫ mu.φ := by
  subst h
  refine ⟨MulEquiv.ofBijective (pushHom mu.cart (Over.mk q)) ⟨fun a b hab => ?_, fun a => ?_⟩, fun g => rfl⟩
  · exact Over.OverMorphism.ext (mu.cart.1.hom_ext (congrArg (fun z => z.left) hab)
      ((Over.w a).trans (Over.w b).symm))
  · obtain ⟨w, h1, h2⟩ := OpenReg.exists_lift mu q a.left (Over.w a)
    exact ⟨Over.homMk w h1, Over.OverMorphism.ext h2⟩

theorem dualMap_alg {O O' : Type} [CommRing O] [CommRing O'] (φ : O →+* O') :
    spMap (dualMap φ) ≫ spMap (algebraMap O (DualNumber O)) =
      spMap (algebraMap O' (DualNumber O')) ≫ spMap φ := by
  rw [OpenReg.spMap_comp, OpenReg.spMap_comp, GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]

end GlobalTheory.ShFam.LatPush
