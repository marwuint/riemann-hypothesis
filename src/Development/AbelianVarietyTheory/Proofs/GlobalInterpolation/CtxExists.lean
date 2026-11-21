import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem ctx_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (N : ℕ) (a : Fin N → F), (∀ l, a l ≠ 0) → ∃ lam ν, Ctx ψ lam ν a := by
  intro F _ _ hF ψ hψ N a ha
  obtain ⟨lam, hlam⟩ := _root_.GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  obtain ⟨ν, hν⟩ := _root_.GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  refine ⟨lam, ν, ?_⟩
  unfold Ctx
  exact ⟨hF, hψ, hlam, hν, ha⟩

end GlobalTheory.SWQ
