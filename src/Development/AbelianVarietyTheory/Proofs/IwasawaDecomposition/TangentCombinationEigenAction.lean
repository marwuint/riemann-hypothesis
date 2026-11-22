import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

noncomputable section

namespace GlobalTheory.FlagEmb

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {R : Type} [CommRing R] {x : Sp R ⟶ X}

theorem eig_of_comb {n : ℕ} (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R)
    (hu : ∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j)
    (h : IsCombAtG t x u cf w) : w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w := by
  have e := (isCombAtG_iff t x (fun j => ovT (hu j).1) cf w).1 h
  have := t.act.hom a
  have h2 := combT_eig x (fun j => ovT (hu j).1) (t.act.act a) r
    (fun j => Over.OverMorphism.ext (hu j).2) cf
  subst e
  exact congrArg (fun φ => φ.left) h2

end GlobalTheory.FlagEmb
