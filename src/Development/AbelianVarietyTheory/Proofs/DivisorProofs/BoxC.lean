import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topC {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) :=
  u.submatrix id (finSumFinEquiv ∘ Sum.inl)

end GlobalTheory.DblDatum
end
