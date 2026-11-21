import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Formalism.LocalToGlobal.Divisibility.TupUsed

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.Reads

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

set_option maxHeartbeats 2000000 in

theorem liftGroupForms_eq_extended_rationalForms_companion (x : TwIn ex) : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) := by
  intro μ hμ i v
  have key : ∀ (t : x.T) (μ : D.what₂.Tup) (e : x.Y.tup t = μ) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (e' : x.Y.tupT μ = t)
      (v : D.what₂.MtL μ ((i : ℕ) + 1)),
      HEq (x.Y.IL.jMt μ hμ i (D.what₂.jMt μ ((i : ℕ) + 1) v)).1
        (x.R.toRealDat.extV i t (x.R.toRealDat.jV i t (liftForm x.A3.A x.F.P0 x.F.ψ0 i t ((x.Y.eMt i t).symm (e.symm ▸ v))))) := by
    intro t μ e hμ e' v
    subst e
    have := x.Y.mtRead i t hμ ((x.Y.eMt i t).symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact heq_of_eq this
  have := eq_of_heq (key _ μ (x.Y.tupTie μ hμ) hμ rfl v)
  rw [this]
  unfold twPOf
  rw [dif_pos hμ]
  rfl

end GlobalTheory.Mem.R3.Reads

end
