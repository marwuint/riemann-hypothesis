import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAdd
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducible
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRoot
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine _root_.GlobalTheory.BI.isChar_induction L L G (fun a => IsChar K L a) (_root_.GlobalTheory.BI.isChar_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (_root_.GlobalTheory.BI.isChar_zero_and_add K L G).2 φ c ?_ hc
      rcases _root_.GlobalTheory.BI.irrChar_linear_or_induced L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact _root_.GlobalTheory.BI.isChar_linear K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine _root_.GlobalTheory.BI.isChar_ind K L G T ψ (ih _ hlt T rfl ?_ (_root_.GlobalTheory.BI.AbByP.subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
