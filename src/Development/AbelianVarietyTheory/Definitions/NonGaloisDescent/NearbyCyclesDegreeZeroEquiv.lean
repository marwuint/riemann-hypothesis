import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace GlobalTheory.FNC

variable (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]

section Formal

variable (O : Type) [CommRing O] [Algebra O K]

theorem coe_aut_one (A : Type) [CommRing A] [Algebra O A] :
    ((1 : A ≃ₐ[O] A) : A →ₐ[O] A) = AlgHom.id O A := rfl

theorem coe_aut_mul {A : Type} [CommRing A] [Algebra O A] (e e' : A ≃ₐ[O] A) :
    ((e * e' : A ≃ₐ[O] A) : A →ₐ[O] A) = (e : A →ₐ[O] A).comp (e' : A →ₐ[O] A) := rfl

end Formal

end GlobalTheory.FNC

end
