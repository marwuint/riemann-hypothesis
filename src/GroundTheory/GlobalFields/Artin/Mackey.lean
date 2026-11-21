import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.TateCohomology.DoubleCosetSum
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

variable {G : Type*} [Group G]

section ExtendByZero

theorem mem_conj_smul_iff (H : Subgroup G) (a g : G) :
    g ∈ (MulAut.conj a • H : Subgroup G) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

open Classical in

def extendByZero (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then f ⟨g, h⟩ else 0

theorem extendByZero_of_mem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ := by
  unfold extendByZero
  rw [dif_pos hg]

@[simp]
theorem extendByZero_coe (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h :=
  extendByZero_of_mem H f h.2

end ExtendByZero

end GroundTheory.Global.Artin
