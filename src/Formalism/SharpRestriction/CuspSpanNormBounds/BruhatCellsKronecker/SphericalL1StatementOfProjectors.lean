import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.RealPlaceAnalysis.LminorPos

open MeasureTheory Matrix Topology Metric Kronecker

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.REAL

namespace L1

section Growth

variable {n : ℕ}

def Lc {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) Q ℂ →ₗ[ℂ] Matrix (Fin n) Q ℂ where
  toFun x := g * x
  map_add' := Matrix.mul_add g
  map_smul' c x := by simp

abbrev RE (n : ℕ) (Q : Type) := Fin n → Q → ℂ

def Re_ (n : ℕ) (Q : Type) : RE n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ := Matrix.ofLinearEquiv ℝ

def RL {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : RE n Q →ₗ[ℝ] RE n Q :=
  ((Re_ n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] RE n Q) ∘ₗ ((Lc (Q := Q) g).restrictScalars ℝ) ∘ₗ
    ((Re_ n Q : RE n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ) : RE n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ)

lemma RL_apply {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : RE n Q) :
    RL g x = Matrix.of.symm (g * Matrix.of x) := rfl

end Growth

end L1

open L1

end Formalism.MainNotions.BridgeLemma

end
