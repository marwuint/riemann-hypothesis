import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem mulVec_sec_split {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {n : ℕ} (g : Matrix (Fin n) (Fin n) (AE D)) (w : Fin n → k) :
    g *ᵥ (fun i => q.sec (w i)) = fun i => q.sec ((g.map q.pr *ᵥ w) i) := by
  funext i
  simp only [mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := GlobalTheory.LocMod.PinEx.sec_mul q (q.pr (g i j)) (w j)
  have h2 := q.sec_pr (g i j)
  have h3 : q.e * q.sec (w j) = q.sec (w j) := by
    have := q.sec_pr (q.sec (w j))
    rw [q.pr_sec] at this
    exact this.symm
  rw [← h1, h2, mul_assoc, mul_left_comm, h3]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

end GlobalTheory.Core.Mi.LatMatch
