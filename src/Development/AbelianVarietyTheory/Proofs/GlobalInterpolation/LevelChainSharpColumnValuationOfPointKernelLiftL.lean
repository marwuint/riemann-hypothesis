import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

end GlobalTheory.LvT.TwColumn
