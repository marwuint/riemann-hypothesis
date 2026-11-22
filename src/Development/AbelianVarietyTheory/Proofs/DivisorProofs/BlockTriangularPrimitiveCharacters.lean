import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradical
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

end GlobalTheory.FinGL.LeviChar
