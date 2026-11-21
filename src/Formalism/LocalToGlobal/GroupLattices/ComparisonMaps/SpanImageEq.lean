import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainKMem
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

abbrev FormsJ (j : ℕ) : Type := FormsLL (Fl.Pj j) (Lv.comp j) (c.embW u w h) (Lv.Int j)

variable {c Tw u w h Lv}

def DescUp (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) : Prop :=
  ∀ j, j + 1 ≤ D.R.m → MRatSpan (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (Lv.Int (j + 1))

end Formalism.L2.G.Cmp
