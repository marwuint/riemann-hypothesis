import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def detA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* AE F E :=
  Matrix.detMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

end GlobalTheory.Published.LeviCentreModel

end
