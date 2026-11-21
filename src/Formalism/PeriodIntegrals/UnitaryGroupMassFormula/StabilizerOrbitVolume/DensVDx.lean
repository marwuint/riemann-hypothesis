import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVNA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSecSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSS

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem gramR_add_sub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (x + W) - gramR R σ J x - gramR R σ J W = gramB R σ J x W := by
  funext i j
  simp [gramR, gramB, hR, Formalism.UG.hform, Matrix.sub_apply, Matrix.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib] <;> ring

theorem gramB_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W W' : Fin n → Fin M → R ⊗[F] E) :
    gramB R σ J x (W + W') = gramB R σ J x W + gramB R σ J x W' := by
  funext i j
  simp [gramB, hR, Formalism.UG.hform, Matrix.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

end PI.VolStabSW
