import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace

variable {D : D7} {c : Comm D} {v : VCom c}

def IsMatrixInFrameOfXZero (G : GLoc v) (κ : GA D (c.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) G.k) : Prop :=
  (mt (c.X 0) κ).map G.q.pr = (G.FX 0 (Nat.zero_le _)).β * g.val * (G.FX 0 (Nat.zero_le _)).γ

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end GlobalTheory.FamTrace

end
