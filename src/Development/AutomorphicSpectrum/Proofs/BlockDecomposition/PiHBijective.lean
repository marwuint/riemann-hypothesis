import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH

universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatCohProd

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}

def tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) : Cn (piF F) n :=
  fun s i => g i s

theorem pull_tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) (i : ι) :
    (piProj F i).pullC n (tup F n g) = g i := rfl

end GlobalTheory.CompanionTheory.CatCohProd
