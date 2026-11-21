import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.ExistsSecCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y : Scheme.{0}}

def pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage y).hom

theorem spMap_pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : spMap (pre y) = y := Spec.map_preimage y

theorem pre_spMap {B : Type} [CommRing B] (ρ : R →+* B) : pre (spMap ρ) = ρ :=
  congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom ρ))

theorem pre_comp {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Sp R) :
    pre (spMap ρ ≫ y) = ρ.comp (pre y) := by
  conv_lhs => rw [← spMap_pre y, ← GlobalTheory.Cris.spMap_comp, pre_spMap]

@[reducible] def ptOf (s : X ⟶ Sp R) {B : Type} [CommRing B] (x : Sp B ⟶ X) : Pt s where
  B := B
  alg := (pre (x ≫ s)).toAlgebra
  x := x
  w := (spMap_pre _).symm

def homOf (s : X ⟶ Sp R) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) (x' : Sp B' ⟶ X)
    (h : spMap ρ ≫ x = x') : ptOf s x ⟶ ptOf s x' :=
  letI : Algebra R B := (pre (x ≫ s)).toAlgebra
  letI : Algebra R B' := (pre (x' ≫ s)).toAlgebra
  { ρ := { ρ with
      commutes' := fun r ↦ by
        change ρ (pre (x ≫ s) r) = pre (x' ≫ s) r
        rw [← h, Category.assoc, pre_comp]
        rfl }
    pt := h }

variable {s : X ⟶ Sp R}

def cv (z : Z1 (FP s)) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) : B' :=
  z.1 _ _ (homOf s ρ x _ rfl)

section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']

theorem cv_add (z z' : Z1 (FP s)) (ρ : B →+* B') (x : Sp B ⟶ X) : cv (z + z') ρ x = cv z ρ x + cv z' ρ x := rfl

end

end CrystallinePoints.Pd
