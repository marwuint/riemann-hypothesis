import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulOneSubLeChoose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOnOpenCuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop.ShareRowsNef

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := by
  refine ⟨fun τ => ?_, fun τ => h τ _ (by omega)⟩
  have key : ∀ (n : ℕ) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + n → la τ b ≤ la τ a := by
    intro n
    induction n with
    | zero => intro a b e; rw [show b = a from Fin.ext e]
    | succ n ih =>
      intro a b e
      have hb := b.2
      have h1 := ih a ⟨a + n, by omega⟩ rfl
      have h2 := h τ (a + n) (by omega)
      rw [gap_eq (la τ) (i := ⟨a + n, by omega⟩) (j := b) e] at h2
      omega
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := by
  have h3 : GapGe 3 P.u₁ := h.gaps.mono (by
    have : 3 * 1 ≤ (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this)
  have h2 : ∀ τ k, k + 1 < Dw.p + Dw.q → 3 ≤ gap (P.u₂ τ) k := fun τ k hk => by
    have a := h3 τ k hk
    have b := (P.gap_rem τ k).1
    simp only [gap, dif_pos hk, WtPar.u₂, Pi.add_apply] at a b ⊢
    omega
  refine ⟨h3.mono (by norm_num), fun τ k hk => le_trans (by norm_num) (h2 τ k hk), fun j τ k hk => ?_⟩
  have a := h3 τ k hk
  have b := h2 τ k hk
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by
    simp only [gap, dif_pos hk, FlagTan.kap]
    split_ifs <;> push_cast <;> omega
  simp only [gap, dif_pos hk, WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply] at a b c ⊢
  simp only [nsmul_eq_mul]
  have e1 := mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) (le_trans (by norm_num) a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans (by norm_num) a)
  nlinarith

theorem two_le_dimFlag (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (hf : 2 < Module.finrank ℚ E / 2) : 2 ≤ FlagTan.dimFlag Dw := by
  unfold FlagTan.dimFlag
  have : 1 ≤ (Dw.p + Dw.q).choose 2 := Nat.choose_pos (by omega)
  nlinarith

end Weights

end GlobalTheory.CovTop.ShareRowsNef

end
