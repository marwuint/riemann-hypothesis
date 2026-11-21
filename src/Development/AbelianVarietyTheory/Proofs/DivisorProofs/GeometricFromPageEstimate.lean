import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsHoldOfTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumOfFjEqOfRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

end GlobalTheory.BigOn
