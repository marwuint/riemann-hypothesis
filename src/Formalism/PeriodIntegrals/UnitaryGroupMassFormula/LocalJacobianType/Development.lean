import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v

def SplitHyp : Prop :=
  Module.finrank F E = 2 ∧ σ ≠ AlgHom.id F E ∧ ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

def VolPP : Prop :=
  ∀ (g r T T' : ℕ) (m : ℝ), SplitHyp σ v → 0 < g → (g : ℤ) ∣ ((T : ℤ) - T') →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l)).toReal =
          m * absV v (g : Fv F v) ^ 3 * (absV v (alp v r l) ^ 4)⁻¹

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

end PI.UnitaryGroupMassFormula.LocJacTyp
