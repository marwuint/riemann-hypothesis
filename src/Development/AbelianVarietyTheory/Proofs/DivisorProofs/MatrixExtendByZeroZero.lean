import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LeviIdx

open GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

def ext0 (M : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := M.map (tensAt E v)

theorem ext_zero_transpose (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

end Lift

end GlobalTheory.LeviIdx

end
