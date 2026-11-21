import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RSFT.GaussPlane

section Helpers

open NumberField.mixedEmbedding
open scoped FourierTransform RealInnerProductSpace

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (by
    rw [Subsingleton.elim w.1 Rat.infinitePlace]; exact Rat.isReal_infinitePlace)⟩

end Helpers

end GlobalTheory.CompanionTheory.RSFT.GaussPlane
