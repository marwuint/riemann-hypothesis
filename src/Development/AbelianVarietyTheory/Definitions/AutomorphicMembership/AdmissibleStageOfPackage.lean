import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

instance intO_valRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing (intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  by_cases h : ‖(a : C)‖ ≤ ‖(b : C)‖
  · by_cases hb : (b : C) = 0
    · refine ⟨1, Or.inr (Subtype.ext ?_)⟩
      rw [hb, norm_zero, norm_le_zero_iff] at h
      simp [h, hb]
    · refine ⟨⟨a / b, show ‖(a / b : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩,
        Or.inr (Subtype.ext ?_)⟩
      simp [mul_div_cancel₀ _ hb]
  · have ha : (a : C) ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨⟨b / a, show ‖(b / a : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ (le_of_not_ge h) (norm_nonneg _)⟩,
      Or.inl (Subtype.ext ?_)⟩
    simp [mul_div_cancel₀ _ ha]

instance intO_frac (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

end Pts

end GlobalTheory.ShFam.Pad.Test
