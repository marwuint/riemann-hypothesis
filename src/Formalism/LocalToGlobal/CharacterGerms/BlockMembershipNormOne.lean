import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIof {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o : Orb) (g : Fin 2) : Type :=
  Σ t : ZMod d, Fin (r (tau o g t))

section Defs

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
  {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]

def blkProd (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : MvPolynomial (Fin n × WVO I) C :=
  ∏ o, toAll o (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o))

end Defs

end Formalism.L2.FormalSeriesBounds.RF
