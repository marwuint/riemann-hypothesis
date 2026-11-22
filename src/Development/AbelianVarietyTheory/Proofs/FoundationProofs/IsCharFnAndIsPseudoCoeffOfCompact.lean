import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

variable {H : Type} [Group H] [TopologicalSpace H]
  {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] {D : H →* (V →L[ℂ] V)} {π : H →* (U →L[ℂ] U)}

variable [MeasurableSpace H] [BorelSpace H] {μ : Measure H}

variable [IsTopologicalGroup H] [CompactSpace H] [μ.IsHaarMeasure]

theorem integral_conj_trace_mul_trace (hD : IsUnitaryRep D) (hi : IsTopIrreducible D) :
    ∫ g, conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ = μ.real univ := by
  let ρ : Representation ℂ H V := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D
  have := hi.1
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)⟩
  have : ρ.IsIrreducible := ⟨fun S => (hi.2 S.toSubmodule ⟨S.toSubmodule.closed_of_finiteDimensional,
    fun g v hv => S.apply_mem_toSubmodule g hv⟩).imp (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h⟩
  have h := integral_conj_character_mul_character_self (haarProb H) ρ hD.continuous_apply hD.norm_apply
  conv_lhs => rw [eq_smul_haarProb μ]
  rw [integral_smul_measure]
  exact (congrArg _ h).trans (by simp [Measure.real])

end GlobalTheory.Orb
