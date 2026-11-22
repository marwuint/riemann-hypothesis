import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.BlockTriLine

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

variable (F E) in

def placeToAdeles (w : InfinitePlace F) : w.Completion ⊗[F] E →ₙ+* AE F E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)).comp
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w))

end Adelic

end GlobalTheory.LeviHC.BlockTriLine
