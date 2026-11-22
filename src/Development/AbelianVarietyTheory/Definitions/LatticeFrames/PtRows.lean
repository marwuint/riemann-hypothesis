import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.MiS

namespace GlobalTheory.Fam

@[reducible] def packB {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) : RealPack O.ex :=
  letI := b.B.alg
  { R := b.R, S := b.S, P := b.P, Dcf := b.C.c.face, Spf := b.C.Sp, Zscf := GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c,
    Ks := b.B.T.Q.c.F, Q := b.B.Q }

end GlobalTheory.Fam

end
