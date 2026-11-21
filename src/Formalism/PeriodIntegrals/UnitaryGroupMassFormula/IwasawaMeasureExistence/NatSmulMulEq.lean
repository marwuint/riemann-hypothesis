import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdeleRing

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

end Cpt

end PI.IwaMeasEx.Wau

end

namespace PI.IwaMeasEx.Wau

namespace Cpt

end Cpt

end PI.IwaMeasEx.Wau

