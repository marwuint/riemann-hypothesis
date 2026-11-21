import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZer
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_ind : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L),
    IsChar K L ψ → IsChar K L (ind H ψ) := by
  intro K L _ _ _ _ _ G _ _ H ψ h
  have hcl : ∀ a x : H, ψ (x⁻¹ * a * x) = ψ a := (_root_.GlobalTheory.isChar_restrict_conj_one K L H ψ h).2.1
  have e : ind H ψ = fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) :=
    funext (_root_.GlobalTheory.BI.ind_eq_finsum_cosets L G H ψ hcl)
  rw [e]
  exact _root_.GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar K L G H ψ h
end GlobalTheory.BI
