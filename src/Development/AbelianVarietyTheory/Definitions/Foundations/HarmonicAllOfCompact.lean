import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def charAct (p q : ℕ) (c : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((c : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight 1

theorem charAct_apply (p q : ℕ) (c : ℚ) (Z : Mat p q) (v : ℂ) :
    charAct p q c Z v = (c : ℂ) * Z.trace * v := by
  simp [charAct]

theorem mem_wt (p q : ℕ) (c : ℚ) (μ : Ix p q → ℚ) (v : ℂ) :
    v ∈ wtSub (charAct p q c) μ ↔ ∀ a, (c : ℂ) * v = μ a * v := by
  simp [wtSub, charAct_apply, Eab, sub_eq_zero]

@[reducible] def charMod (p q : ℕ) (c : ℚ) : GKMod p q where
  V := ℂ
  act := charAct p q c
  lie := by
    intro X Y
    ext
    simp [charAct_apply, Matrix.trace_mul_comm X Y]; ring
  kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => Submodule.mem_iSup_of_mem (fun _ => c) ((mem_wt _ _ _ _ _).2 fun _ => rfl)

def vac : Pol 1 0 1 0 →ₗ[ℂ] TensorProduct ℂ (charMod 1 0 (1 / 2)).V (charMod 1 0 (1 / 2)).V :=
  (lcoeff ℂ 0).smulRight ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ)

end GlobalTheory.FockAlg.Model
