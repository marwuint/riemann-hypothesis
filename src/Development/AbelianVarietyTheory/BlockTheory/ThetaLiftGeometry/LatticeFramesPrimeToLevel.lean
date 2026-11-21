import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

end Adelic

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
