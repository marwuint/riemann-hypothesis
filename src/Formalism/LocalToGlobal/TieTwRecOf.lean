import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.FiniteTOf
import Formalism.LocalToGlobal.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top4

open Formalism.L2.Top3

section TwPl

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tw_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.Tw = S1.Tw := by
  subst h; cases eq_of_heq hS; rfl

end TwPl

end Formalism.L2.Top4

end
