import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

section Pair

variable {R : Type} [CommRing R]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_transpose (σ : κ ≃ α × β) (X : Matrix α β R) : flat (σ.trans (Equiv.prodComm α β)) Xᵀ = flat σ X := rfl

end Pair

end GlobalTheory.WeilM

end
