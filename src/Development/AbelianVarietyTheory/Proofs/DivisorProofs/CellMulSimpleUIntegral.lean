import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKFactor.UnitaryInt

open GlobalTheory.GKFactor

variable {L : Type} [Field L] {n : ℕ}

local notation "M" x:max => ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem mem_GLint_iff_entries (O : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) O ↔ (∀ i j, (M g) i j ∈ O) ∧ ∀ i j, (M g⁻¹) i j ∈ O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

end GlobalTheory.GKFactor.UnitaryInt
