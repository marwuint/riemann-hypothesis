import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

def absNormUnits : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ →* ℝˣ :=
  Units.map (((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ).comp
    (FractionalIdeal.absNorm : FractionalIdeal (𝓞 ℚ)⁰ ℚ →*₀ ℚ).toMonoidHom)

theorem coe_absNormUnits (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
    ((absNormUnits I : ℝˣ) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℚ) : ℝ) := rfl

end GlobalTheory.CompanionTheory.RSFT

end
