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

theorem absFrob_comm {k : Type} [Field k] [Fintype k] {X Y : Over (Sp k)} (f : X.left ⟶ Y.left) :
    absFrob X ≫ f = f ≫ absFrob Y := by
  refine Scheme.Hom.ext rfl fun U => ?_
  ext a
  have e : (X.left.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ U = f ⁻¹ᵁ U)).op).hom (((f.app U).hom a) ^ Fintype.card k) =
      (f.app U).hom (a ^ Fintype.card k) := by simp
  exact e

theorem absFrob_base (k : Type) [Field k] [Fintype k] (X : Over (Sp k)) [IsIso X.hom] : absFrob X = 𝟙 _ := by
  rw [← cancel_mono X.hom, absFrob_comm (Y := Over.mk (𝟙 _)) X.hom, Category.id_comp]
  have : absFrob (Over.mk (𝟙 (Sp k))) = 𝟙 (Sp k) := by
    haveI : IsAffine (Over.mk (𝟙 (Sp k))).left := inferInstanceAs (IsAffine (Spec _))
    apply ext_of_isAffine
    ext a
    obtain ⟨c, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of k))) (W := ⊤) rfl).2 a
    exact (map_pow (cst (𝟙 (Spec (CommRingCat.of k))) ⊤) c _).symm.trans (congrArg _ (FiniteField.pow_card c))
  rw [this]
  exact Category.comp_id _

def frobOver {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) : X ⟶ X :=
  Over.homMk (absFrob X) (by
    have := absFrob_comm (Y := Over.mk (𝟙 _)) X.hom
    haveI hI : IsIso (Over.mk (𝟙 (Sp k))).hom := inferInstanceAs (IsIso (𝟙 _))
    rw [absFrob_base k (Over.mk (𝟙 _))] at this
    exact this.trans (Category.comp_id _))

end GlobalTheory.SS.FrobModel
end
