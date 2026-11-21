import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFDual

open Ad3 Ad3.LFS

section Inst

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

instance secondCountable_units : SecondCountableTopology Fˣ :=
  (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology

instance locallyCompact_units : LocallyCompactSpace Fˣ :=
  (isOpenEmbedding_units_val (K := F)).locallyCompactSpace

instance secondCountable_GL2 : SecondCountableTopology (GL (Fin 2) F) :=
  (Measures.isOpenEmbedding_val F 2).isEmbedding.secondCountableTopology

instance locallyCompact_gl_two : LocallyCompactSpace (GL (Fin 2) F) :=
  (Measures.isOpenEmbedding_val F 2).locallyCompactSpace

variable [MeasurableSpace F] [BorelSpace F]

instance isHaar_hG (ψ : AddChar F Circle) : (hG ψ).IsHaarMeasure := by
  unfold hG; infer_instance

instance sigmaFinite_hG (ψ : AddChar F Circle) : SigmaFinite (hG ψ) := inferInstance

instance sigmaFinite_sd (ψ : AddChar F Circle) : SigmaFinite (selfDualMeasure ψ) := inferInstance

instance sigmaFinite_plane_measure_alt (ψ : AddChar F Circle) : SigmaFinite (vol2 ψ) := by
  unfold vol2; infer_instance

instance sigmaFinite_multHaar : SigmaFinite (multHaar F) := inferInstance

end Inst

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

def rho : Measure Fˣ :=
  (multHaar F).withDensity fun τ =>
    ENNReal.ofReal (((multHaarConst F).toReal)⁻¹ * (modulus (τ : F) : ℝ) ^ 2)

instance sFinite_rho : SFinite (rho F) := by
  unfold rho; infer_instance

end D

end GlobalTheory.CompanionTheory.LFDual
