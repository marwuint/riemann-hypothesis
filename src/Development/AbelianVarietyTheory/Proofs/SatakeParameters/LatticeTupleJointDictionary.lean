import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDet
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (_root_.GlobalTheory.TwV.Joint.isPt_pt_zero t std J La).1
    exact ⟨hp, _root_.GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul t std J La hLa, _root_.GlobalTheory.kerN_zero_eq_latK_pt t std J La, _root_.GlobalTheory.joint_dt_eq_det_of_isPt t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (_root_.GlobalTheory.TwV.Joint.pt_succ_isPt t std J j hj La).1
    exact ⟨hp, _root_.GlobalTheory.TwV.Joint.pt_succ_coset t std J j hj La hLa, _root_.GlobalTheory.TwV.Joint.kerN_succ_heq t std J j hj La hLa, _root_.GlobalTheory.joint_dt_eq_det_of_isPt t std J (j + 1) hj La _ hp⟩
