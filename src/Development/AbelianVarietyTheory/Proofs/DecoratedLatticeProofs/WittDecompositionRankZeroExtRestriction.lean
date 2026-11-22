import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory GlobalTheory.FinPl.VLast

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VLast.KernPf

variable {D : D7}

theorem wittDecomposition_rankZero_coreEmbed_proj {S S₀ : HSp D} (e : HypDec S S₀ 0) : e.j0 ⬝ e.p0 = 1 := by
  have h := e.sum_eq_one
  have h1 : e.jX ⬝ e.pX = 0 := by ext i k; simp [Matrix.mul_apply]
  have h2 : e.jY ⬝ e.pY = 0 := by ext i k; simp [Matrix.mul_apply]
  rwa [h1, h2, zero_add, add_zero] at h

def wittCoreRestrictionHom {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) : WO S T →+ WO S₀ T where
  toFun w := w ⬝ e.j0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem wittCoreRestrictionHom_apply {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) (w : WO S T) : wittCoreRestrictionHom e T w = w ⬝ e.j0 := rfl

theorem wittDecomposition_rankZero_ext_restriction {S S₀ : HSp D} (e : HypDec S S₀ 0) (T : HSp D) (w : WO S T) : e.ext0 T (wittCoreRestrictionHom e T w) = w := by
  rw [HypDec.matrixExtendByZero_apply, wittCoreRestrictionHom_apply, Matrix.mul_assoc, wittDecomposition_rankZero_coreEmbed_proj, Matrix.mul_one]

end GlobalTheory.FinPl.VLast.KernPf

namespace GlobalTheory.FinPl.VLast.KernPf

end GlobalTheory.FinPl.VLast.KernPf
