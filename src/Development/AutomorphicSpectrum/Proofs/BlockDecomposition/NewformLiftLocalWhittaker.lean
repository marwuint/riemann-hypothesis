import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker

open Ad3 Ad3.R

section Unr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ord_one' : ord (1 : F) = 0 := by
  have := (mem_unitFiltrationUnits_zero_iff_ord (K := F) (u := 1)).1 (one_mem _)
  simpa using this

end Unr

section Glob

theorem wh_eq (φ : G2 → ℂ) (g : G2) :
    Wh φ g = ∫ x in fundamentalSet ℚ, φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ := rfl

end Glob

end GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker
end
