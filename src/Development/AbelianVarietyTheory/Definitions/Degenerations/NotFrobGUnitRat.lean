import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS.ProjLinePlaces
end GlobalTheory.SS.ProjLinePlaces

namespace GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

def powApp {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (U : X.left.Opens) : Γ(X.left, U) →+* Γ(X.left, U) where
  toFun := fun a => a ^ Fintype.card k
  map_one' := one_pow _
  map_mul' := fun a b => mul_pow a b _
  map_zero' := zero_pow Fintype.card_ne_zero
  map_add' := fun a b => by
    letI := (cst X.hom U).toAlgebra
    exact map_add (FiniteField.frobeniusAlgHom k Γ(X.left, U)) a b

def absPsh {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) :
    X.left.toPresheafedSpace ⟶ X.left.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app := fun U => CommRingCat.ofHom (powApp X U.unop)
      naturality := fun U V i => by
        ext a
        exact (map_pow (X.left.presheaf.map i).hom a _).symm }

def absFrob {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) : X.left ⟶ X.left :=
  ⟨{ toHom := absPsh X
     prop := fun x => ⟨fun a ha => by
      obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.left.presheaf (x := x) a
      have h := PresheafedSpace.stalkMap_germ_apply (absPsh X) U x hx s
      have h2 : IsUnit ((X.left.presheaf.germ U x hx).hom (s ^ Fintype.card k)) := by
        have := h ▸ ha
        exact this
      rw [map_pow] at h2
      exact (isUnit_pow_iff Fintype.card_ne_zero).1 h2⟩ }⟩

end GlobalTheory.SS.FrobModel
end
