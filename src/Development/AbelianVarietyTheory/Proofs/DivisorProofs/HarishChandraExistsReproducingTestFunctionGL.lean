import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinityStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity

end GlobalTheory.HCAlphaGL

end
