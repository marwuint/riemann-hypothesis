import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.HodgeGapBounds

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}

theorem bar_lt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega

theorem one_le_gap_uMinus (P : WtPar Dw) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (hs : StrictAnti (P.u₁ τ)) : 1 ≤ gap (P.uMinus τ) (Dw.p - 1) := by
  have hk := bar_lt hp hq
  have h1 := P.gap_u₁ τ hk
  have hT : 0 < P.T₁ := by unfold WtPar.T₁; positivity
  have hg : 1 ≤ gap (P.u₁ τ) (Dw.p - 1) := by
    rw [gap, dif_pos hk]
    have := hs (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p - 1 + 1, hk⟩ from by
      rw [Fin.mk_lt_mk]; omega)
    omega
  rw [h1, Int.le_ediv_iff_mul_le hT, one_mul] at hg
  have hkap : gap (FlagTan.kap Dw τ) (Dw.p - 1) = 2 * ((Dw.p : ℤ) + Dw.q) - 2 := by
    simp only [gap, dif_pos hk, FlagTan.kap, Fin.val_mk]
    have := Nat.cast_sub (R := ℤ) hp
    split_ifs <;> push_cast at * <;> omega
  have hsub : gap ((P.uMinus - FlagTan.kap Dw) τ) (Dw.p - 1) =
      gap (P.uMinus τ) (Dw.p - 1) - gap (FlagTan.kap Dw τ) (Dw.p - 1) := by
    simp only [gap, dif_pos hk, Pi.sub_apply]; ring
  have hT1 : 1 ≤ P.T₁ := hT
  omega

theorem laOf_add_smul (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 s : ℤ) :
    laOf Dw a n + s • hodgeWt Dw =
      uMinus Dw a n kc c0 + (s + c0) • hodgeWt Dw + FlatLine.parWt Dw (anchor Dw a n kc) := by
  rw [← uWt_add_anchor Dw a n kc]
  simp only [uMinus, add_smul]
  abel

theorem gap_add_smul_hodge (v : AllWt.Weight Dw) (x : ℤ) (w : Psi H → ℤ) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    gap ((v + x • hodgeWt Dw + FlatLine.parWt Dw w) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + x := by
  have hk := bar_lt hp hq
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, FlatLine.parWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

theorem antitone_add_par (v : AllWt.Weight Dw) (w : Psi H → ℤ) (τ : Psi H) (h : Antitone (v τ)) :
    Antitone ((v + FlatLine.parWt Dw w) τ) :=
  fun _ _ hab => add_le_add (h hab) le_rfl

end Weights

end GlobalTheory.CovTop.HodgeGapBounds

namespace GlobalTheory.CovTop.HodgeGapBounds

end GlobalTheory.CovTop.HodgeGapBounds
