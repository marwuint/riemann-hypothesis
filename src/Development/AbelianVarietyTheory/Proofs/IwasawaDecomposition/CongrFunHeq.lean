import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

end GlobalTheory.LayerMove
end
