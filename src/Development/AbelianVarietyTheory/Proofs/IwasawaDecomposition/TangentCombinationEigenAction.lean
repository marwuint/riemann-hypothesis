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

theorem existsUnique_comb_change {n : ℕ} {e u : Fin n → Tn t R} (he : ∀ j, IsTanAtG t x (e j))
    (K : Matrix (Fin n) (Fin n) R) (hK : IsUnit K.det) (hu : ∀ j, IsCombAtG t x e (fun i => K i j) (u j))
    {w : Tn t R} (hw : IsTanAtG t x w) (hb : ∃! a, IsCombAtG t x e a w) : ∃! a, IsCombAtG t x u a w := by
  have hU : u = fun j => (combT x (fun i => ovT (he i)) (fun i => K i j)).left :=
    funext fun j => ((isCombAtG_iff t x (fun i => ovT (he i)) _ _).1 (hu j)).symm
  subst hU
  have h2 : ∃! a : Fin n → R, ovT hw = combT x (fun j => ovT (he j)) a := by
    obtain ⟨a, ha, hq⟩ := hb
    exact ⟨a, Over.OverMorphism.ext ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).1 ha).symm,
      fun b hb => hq b ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [← hb]; rfl))⟩
  obtain ⟨a, ha, hq⟩ := reframe_basis x _ (fun j => smT_zero_ovT _) K hK _ h2
  exact ⟨a, (isCombAtG_iff t x _ _ _).2 (by rw [← ha]; rfl),
    fun b hb => hq b (Over.OverMorphism.ext ((isCombAtG_iff t x _ _ _).1 hb).symm)⟩

end GlobalTheory.FlagEmb
