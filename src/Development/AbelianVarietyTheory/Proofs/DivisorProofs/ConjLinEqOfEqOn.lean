import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

end Blocks

def conjE {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) :=
  { conjLin U.toLinearMap with
    invFun := conjLin U.symm.toLinearMap
    left_inv := fun φ => by
      funext x
      simp [conjLin_apply]
    right_inv := fun φ => by
      funext x
      simp [conjLin_apply] }

theorem conjE_apply {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) : conjE U φ = conjLin U.toLinearMap φ := rfl

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem partL_eq_of_eqOn {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ → AF F) → ℂ) → (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partL T Φ = partL e Φ :=
  partL_congr fun b => h _ (sliceL_mem hΦ b)

theorem partR_eq_of_eqOn {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ' → AF F) → ℂ) → (κ₁' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ', T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partR T Φ = partR e Φ :=
  partR_congr fun a => h _ (sliceR_mem hΦ a)

theorem conjLin_eq_of_eqOn {κ κ₁ : Type} [Fintype κ] {T e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) : ∀ Φ ∈ schA F κ, conjLin T Φ = conjLin e Φ := fun Φ hΦ => by
  funext y
  rw [conjLin_apply, conjLin_apply, h _ (GlobalTheory.ConjSch.conj_mem_schA Φ hΦ)]

theorem adm_congr {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ)
    (hl : l' ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => by rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT]⟩

theorem dbl_eq {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partR (conjLin U.toLinearMap) (partL U Φ) = partR (conjLin u) (partL u Φ) ∧
      partR (conjLin u) (partL u Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partL U Φ = partL u Φ := partL_eq_of_eqOn hUu hΦ
  have h2 : partL u Φ ∈ schA F (κ ⊕ κ) := partL_mem u hu Φ hΦ
  refine ⟨?_, partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) _ h2⟩
  rw [h1]
  exact partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) h2

end Gen

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Main

variable {F : Type} [Field F] [NumberField F]

end Main

end GlobalTheory.DblTr
