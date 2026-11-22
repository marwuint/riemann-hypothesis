import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThetaRuleLeLocalValueCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0Statement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetsCharZero

theorem num_le (dF R N r g0 g1 cst : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) (hr : 0 ≤ r) (hg0 : 0 < g0) (hle : g0 ≤ g1)
    (h : R * N ^ 3 * (r * N / 4 + 2 * dF ^ 2) / g0 ≤ cst) : dF ^ 2 * (R * N ^ 3) / g1 ≤ cst := by
  have hX : 0 ≤ R * N ^ 3 := by positivity
  refine le_trans ?_ h
  calc dF ^ 2 * (R * N ^ 3) / g1 ≤ dF ^ 2 * (R * N ^ 3) / g0 := div_le_div_of_nonneg_left (by positivity) hg0 hle
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hg0.le
        have : dF ^ 2 ≤ r * N / 4 + 2 * dF ^ 2 := by nlinarith [sq_nonneg dF, mul_nonneg hr hN]
        nlinarith [mul_le_mul_of_nonneg_left this hX]

theorem exists_thRule_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → 1 ≤ n → ∀ (N cst : ℝ), ((Module.finrank ℚ E * Dw.q : ℕ) : ℝ) ≤ N → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * (2 * Real.sqrt N) < q → (DF Dw a : ℝ) ^ 2 * ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * N ^ 3) / q ≤ cst → ∃ f ∈ thGen Xo c nab a n, evI y f ≠ 0 ∧ (vV T.V (evI y f) : ℝ) ≤ cst * φ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hch φ hφ α q hα hq hMb a n hanti hs hn N cst hρN h4 hM0 hcst
  obtain ⟨P₁, hP₁, hB⟩ := GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 E H Dw l Xo c a n hanti hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData E H Dw l Xo c T io y C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.ShortPhi.exists_shortBasis E H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  set R : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) with hR
  have hR0 : 0 ≤ R := by positivity
  have hρN' : (ρ : ℝ) ≤ N := le_trans (by exact_mod_cast hρ) hρN
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := hρ0.trans hρN'
  have hM0' : (DF Dw a : ℝ) * (2 * Real.sqrt ρ) < q := lt_of_le_of_lt (by gcongr) hM0
  have hup := GlobalTheory.T.iInf_thetaRule_le_localValue_charZero E H Dw l Xo c nab hnab T io y C hTr P hP hch ϖ hϖ Q hQ ρ _ _ hSB α q hα hq hMb a n 1 hn one_pos h4
    hM0' P₁ hP₁
  have hloc := hB T io y C hch 1 l.M one_pos
  have hφ0 := hφ.nonneg
  have hq0 : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  set B : ℝ := (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q / ((1 : ℕ) : ℝ) with hBdef
  have hBle : B ≤ cst * φ := by
    rw [hBdef, Nat.cast_one, div_one]
    calc (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q ≤ (DF Dw a : ℝ) ^ 2 * (R * N ^ 3 * φ) / q := by gcongr
      _ = (DF Dw a : ℝ) ^ 2 * (R * N ^ 3) / q * φ := by ring
      _ ≤ cst * φ := by gcongr
  have hinf : (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f)) ≤
      ((B : ℝ) : EReal) := by
    refine hup.trans ?_
    calc _ ≤ (0 : EReal) + ((B : ℝ) : EReal) := add_le_add hloc le_rfl
      _ = _ := zero_add _
  by_contra hne
  push_neg at hne
  have hlow : (((⌊B⌋ + 1 : ℤ) : ℝ) : EReal) ≤
      ⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen Xo c nab a n := ⟨x, P₁, hP₁, hx⟩
    by_cases h0 : evI y f = 0
    · rw [h0, nval_zero]; exact le_top
    have h1 := hne f hf h0
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_le_coe_iff]
    have h2 : B < (vV T.V (evI y f) : ℝ) := lt_of_le_of_lt hBle h1
    have h3 : ⌊B⌋ < vV T.V (evI y f) := Int.floor_lt.2 h2
    exact_mod_cast h3
  have h5 := EReal.coe_le_coe_iff.1 (hlow.trans hinf)
  push_cast at h5
  linarith [Int.lt_floor_add_one B]

end GlobalTheory.JetsCharZero

end
