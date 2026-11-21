import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatPieces

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type t} (c : C → ι)

abbrev piece (i : ι) : ObjectProperty C := fun T => c T = i

abbrev res (i : ι) : Mor F ((ObjectProperty.ι (piece c i)) ⋙ F) (RingHom.id R) :=
  Mor.restrict F (ObjectProperty.ι (piece c i))

variable {c}

theorem chain_piece (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (s : ComposableArrows C n)
    (k : Fin (n + 1)) : c (s.obj k) = c (s.obj 0) :=
  (hc (s.map (homOfLE (Fin.zero_le k)))).symm

variable {F}

def glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) : Cn F n :=
  fun s => g (c (s.obj 0)) (ObjectProperty.lift (piece c (c (s.obj 0))) s (chain_piece hc s))

theorem glue_pullC (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (f : Cn F n) :
    glue hc (fun i => (res F c i).pullC n f) = f := rfl

end GlobalTheory.CompanionTheory.CatPieces

