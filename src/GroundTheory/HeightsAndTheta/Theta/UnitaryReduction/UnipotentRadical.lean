import Mathlib
import GroundTheory.AutomorphicForms.UnitaryGroupScheme
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.MemRangeIffIsIntegral
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

open NumberField GroundTheory.Automorphic Module TensorProduct Matrix FunctionalEquationAlt

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

section Rational

variable (B : HermitianForm F E V)

def perp (W : Submodule E V) : Submodule E V := W.orthogonalBilin B.toSesq

end Rational

section Example

variable (F E)

def hypPlaneSesq : (Fin 2 → E) →ₛₗ[conjHom F E] (Fin 2 → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E (x 0) * y 1 + conj F E (x 1) * y 0)
    (by intros; simp only [Pi.add_apply, map_add]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [show ∀ c, conjHom F E c = conj F E c from fun _ => rfl]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem hypPlaneSesq_apply (x y : Fin 2 → E) :
    hypPlaneSesq F E x y = conj F E (x 0) * y 1 + conj F E (x 1) * y 0 := rfl

end Example

end UnitaryReduction

end GroundTheory.Heights₂.Theta
