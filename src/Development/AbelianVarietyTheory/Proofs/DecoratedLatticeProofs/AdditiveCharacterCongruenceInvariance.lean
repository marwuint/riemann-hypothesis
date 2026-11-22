import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryPsiValue

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiColSide

theorem psi_unif_mul_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : GlobalTheory.SymChain.SymData k s κ) (d e : k) (hv : valuation k (d - e) < 1) :
    (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * e) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * d) : ℂ) := by
  have hsplit : ((S.ϖ⁻¹ : kˣ) : k) * d = ((S.ϖ⁻¹ : kˣ) : k) * e + ((S.ϖ⁻¹ : kˣ) : k) * (d - e) := by ring
  have h1 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (d - e)) = 1 := by
    refine (S.cond 1).2 le_rfl _ ?_
    have hle := (S.unif _).1 hv
    have hϖ : valuation k ((S.ϖ : kˣ) : k) ≠ 0 := by simp
    rw [map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    calc (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k (d - e)
        ≤ (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k ((S.ϖ : kˣ) : k) := by gcongr
      _ = 1 := inv_mul_cancel₀ hϖ
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one]

end GlobalTheory.FamTraceChiColSide

end
