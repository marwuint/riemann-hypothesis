import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.ShortSpanUnitCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem abs_kap_le (Dw : Datum H) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(FlagTan.kap Dw τ k : ℝ)| ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
  have hk := k.2
  have h : |FlagTan.kap Dw τ k| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
    simp only [FlagTan.kap]
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> omega
  rw [← Int.cast_abs]; exact_mod_cast h

theorem sum_abs_kap_le (Dw : Datum H) :
    ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
  calc ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ ∑ _τ : Psi H, ∑ _k : Fin (Dw.p + Dw.q), ((Dw.p + Dw.q : ℕ) : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => abs_kap_le Dw τ k
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sum_abs_weightZero_le_components (Dw : Datum H) (P : WtPar Dw) :
    ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| ≤ ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| + ∑ τ, ∑ k, |(P.u₂ τ k : ℝ)| +
      (FlagTan.dimFlag Dw : ℝ) * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => ?_
  have e : (P.wt 0 τ k : ℝ) = (FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ) + (FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ) := by
    simp only [WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [e]
  calc _ ≤ |(FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ)| + |(FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, Nat.abs_cast]
      linarith [abs_add_le (FlagTan.kap Dw τ k : ℝ) (P.u₂ τ k : ℝ)]

theorem consecutiveGap_weightZero_ge (Dw : Datum H) (P : WtPar Dw) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) (g : ℤ)
    (hg : g ≤ gap (P.u₁ τ) k) : ((FlagTan.dimFlag Dw : ℤ) + 1) * g - 2 ≤ gap (P.wt 0 τ) k := by
  have hr := (P.gap_rem τ k).1
  have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
    simp only [FlagTan.kap, Fin.val_mk]
    split_ifs <;> push_cast <;> omega
  rw [gap, dif_pos h] at hr hg ⊢
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply] at hr ⊢
  simp only [nsmul_eq_mul] at hr ⊢
  have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

theorem final_le {C Zr S Dc PP X abelian₂ L : ℝ} (hC : 0 ≤ C) (hL : 4 * C + 1 ≤ L) (hZL : L ≤ Zr) (hPP : Zr ^ 12 ≤ PP)
    (hDc : 1 ≤ Dc) (hX : 1 ≤ X) (hS : S ≤ 3 * Dc * Zr ^ 2 * X) (hLam : Real.log abelian₂ ≤ C * (Zr ^ 3 * S + Zr ^ 5)) :
    Real.log abelian₂ ≤ Dc * PP * X := by
  have hZ1 : 1 ≤ Zr := by linarith
  have hZ0 : 0 ≤ Zr := by linarith
  have hZ5 : 0 ≤ Zr ^ 5 := by positivity
  have hDX : 1 ≤ Dc * X := by nlinarith
  have h1 : Zr ^ 3 * S ≤ 3 * (Dc * X) * Zr ^ 5 := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ Zr ^ 3)
    nlinarith
  have h2 : Zr ^ 5 ≤ (Dc * X) * Zr ^ 5 := by nlinarith
  have h3 : C * (Zr ^ 3 * S + Zr ^ 5) ≤ (Dc * X) * (4 * C * Zr ^ 5) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    nlinarith
  have h4 : 4 * C * Zr ^ 5 ≤ PP := by
    have a : Zr ≤ Zr ^ 7 := by
      calc Zr = Zr ^ 1 := (pow_one _).symm
        _ ≤ Zr ^ 7 := pow_le_pow_right₀ hZ1 (by norm_num)
    have b : 4 * C ≤ Zr ^ 7 := by linarith
    have c : 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := mul_le_mul_of_nonneg_right b hZ5
    calc 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := c
      _ = Zr ^ 12 := by ring
      _ ≤ PP := hPP
  have h5 : (Dc * X) * (4 * C * Zr ^ 5) ≤ (Dc * X) * PP := mul_le_mul_of_nonneg_left h4 (by linarith)
  calc Real.log abelian₂ ≤ _ := hLam
    _ ≤ _ := h3
    _ ≤ _ := h5
    _ = Dc * PP * X := by ring

theorem sum_le {S K A1 A2 Dc W : ℝ} (hSle : S ≤ K + A2 + Dc * A1) (hK : K ≤ W) (h1 : A1 ≤ W) (h2 : A2 ≤ W)
    (hDc : 1 ≤ Dc) (hW : 0 ≤ W) : S ≤ 3 * Dc * W := by
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Dc)
  nlinarith

theorem log_sum_le {S k fr L : ℝ} (hS0 : 0 ≤ S) (hSk : S ≤ (fr * L) ^ 2 * k) (hk : Real.log k ≤ 2 * L)
    (hfr : Real.log fr ≤ L) (hL1 : 1 ≤ L) (hfr1 : 1 ≤ fr) : Real.log S ≤ 10 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hZ : 0 < fr * L := by positivity
  have hk0 : 0 < k := by
    by_contra hk0
    push_neg at hk0
    have : (fr * L) ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk0
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc Real.log S ≤ Real.log ((fr * L) ^ 2 * k) := Real.log_le_log h hSk
    _ = 2 * (Real.log fr + Real.log L) + Real.log k := by
      rw [Real.log_mul (by positivity) hk0.ne', Real.log_pow, Real.log_mul (by linarith) (by linarith)]; push_cast; ring
    _ ≤ 10 * L := by linarith

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

end GlobalTheory.CovTop.ShortSpanUnitCover
