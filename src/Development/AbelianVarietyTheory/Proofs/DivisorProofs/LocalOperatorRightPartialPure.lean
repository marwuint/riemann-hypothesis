import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartREqPartLSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorLeftPartialPure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.DblEval.BlockSwap

theorem partR_pureA {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ]
    [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F),
      ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'),
        partR e (pureA F f g) = pureA F (P f) g₁ :=
  GlobalTheory.DblEval.BlockSwap.partR_of_partL e (_root_.GlobalTheory.DblEval.PartLStr.exists_partL_pureA e he)

end GlobalTheory.DblEval.BlockSwap
