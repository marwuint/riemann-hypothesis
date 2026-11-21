import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVCos
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibOfTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

end PI.VolStabW
