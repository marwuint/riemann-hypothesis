import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealBelow
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartKernel
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncDomain
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial LineChowForm SectionLine

noncomputable section

namespace ChartFracSeparableInhabited

theorem chartLocDomain : ChartLocDomain.Statement :=
  ChartLocDomain.proof (IncIdealBelow.proof ChowFormMultiHomog.full) ChartIncDomain.proof
    (ChartKernel.proof IncidenceGeneric.full ChartIncDomain.proof)

theorem line_domain (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) ∧
      Function.Injective (algebraMap (Localization.AtPrime p)
        (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) := by
  obtain ⟨hdom, hinj, -⟩ := chartLocDomain F 2 1 ⊥ D2 (coeffX1 F) p isProjPrime_line isChowForm_line
    (linearFormX1_ne_zero F)
  exact ⟨hdom, hinj⟩

scoped instance line_isDomain (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) :=
  (line_domain F p).1

scoped instance line_isTorsionFree (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (line_domain F p).2

set_option synthInstance.maxHeartbeats 400000 in

scoped instance line_faithfulSMul (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    FaithfulSMul (Localization.AtPrime p) (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (Localization.AtPrime p)
    (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)]
  rw [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (line_domain F p).2

end ChartFracSeparableInhabited

end

end GroundTheory.Heights₂.Heights
