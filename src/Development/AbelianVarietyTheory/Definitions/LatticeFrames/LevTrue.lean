import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Formalism.LocalToGlobal.IndefiniteReal.RealRec

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (a : GeoAll W u)

structure Cst where
  ε : ℕ → a.ι → 𝓀[a.k]ˣ
  op : ∀ j, BiOp (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1))
  r : ℕ → a.ι → ℝ
  e : ℕ → a.ι → ℤ
  cG : ℕ → ℂ
  sc : W.P.T → ℕ → ℂ

variable {a} (k : Cst a)

variable {row : ∀ t, RowCh (pk W) (lvP W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}

end Gen

end GlobalTheory.Fam

end
