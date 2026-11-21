import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : ℕ) : GL (Fin n) k →* GL (Fin n) k where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_val (n : ℕ) (g : GL (Fin n) k) : (invT n g).val = (g⁻¹).val.transpose := rfl

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

end GlobalTheory.HoweBridge
