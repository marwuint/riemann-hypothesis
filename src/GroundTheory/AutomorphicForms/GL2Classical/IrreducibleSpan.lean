import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.CuspWeights
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslatesIrreducible

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

def IsRot (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = kGL w hw

def IsRefl (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = toReal epsilon * kGL w hw

theorem IsRot.det_pos {x : archCompact ℚ 2} (hx : IsRot x) : 0 < (kMat x).det.val := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h]
  exact det_kGL_pos w hw

theorem IsRefl.det_neg {x : archCompact ℚ 2} (hx : IsRefl x) : (kMat x).det.val < 0 := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h, map_mul, Units.val_mul, det_toReal_epsilon]
  have := det_kGL_pos w hw
  linarith

theorem kMat_mul (x y : archCompact ℚ 2) : kMat (x * y) = kMat x * kMat y :=
  archToReal_mul _ _

abbrev Rop : Module.End ℂ (cuspForms ℚ 2) := cuspOp raiseMat

abbrev Lop : Module.End ℂ (cuspForms ℚ 2) := cuspOp lowerMat

abbrev Jop : Module.End ℂ (cuspForms ℚ 2) := cuspOp rotMat

abbrev Zop : Module.End ℂ (cuspForms ℚ 2) := cuspOp 1

abbrev σc (x : archCompact ℚ 2) : Module.End ℂ (cuspForms ℚ 2) := archCompactRepCusp ℚ 2 x

section Span

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

variable (k) in

def weightEig : ℕ ⊕ ℕ → ℂ
  | Sum.inl j => I * k + 2 * I * j
  | Sum.inr j => -(I * k + 2 * I * j)

end Span

section Stable

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

end Stable

section Extract

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

end Extract

end GL2Classical

end

end GroundTheory.Automorphic
