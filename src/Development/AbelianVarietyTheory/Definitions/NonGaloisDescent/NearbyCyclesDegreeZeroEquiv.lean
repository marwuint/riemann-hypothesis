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

end Formal

end GlobalTheory.FNC

end
