import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHost

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

theorem absA_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ τ k, |(laOf Dw a n τ k : ℝ)| ≤ B) :
    ((GlobalTheory.LevGeo.absA Dw a : ℕ) : ℝ) ≤ (Module.finrank ℚ E : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * B) := by
  have hn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ∀ (b : E →+* ℂ) (i : ℕ), i < Dw.mult b → (a (b, i) : ℝ) ≤ B := by
    intro b i hi
    by_cases hb : b (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, hb] using hi
      have := h ⟨b, hb⟩ ⟨i, by omega⟩
      simp only [laOf, weightOf, if_pos hp, Int.cast_add, Int.cast_natCast] at this
      linarith [le_abs_self ((a (b, i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
    · have hq : i < Dw.q := by simpa [Datum.mult, hb] using hi
      have := h ⟨conjEmb b, conj_mem hb⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
      have e1 : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, weightOf, if_neg e1, e2, conjEmb_conjEmb, Int.cast_sub, Int.cast_neg, Int.cast_natCast] at this
      linarith [neg_abs_le (-(a (b, i) : ℝ) - ((n / 2 : ℕ) : ℝ))]
  unfold GlobalTheory.LevGeo.absA
  rw [Nat.cast_sum, ← NumberField.Embeddings.card E ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
  rw [Nat.cast_sum]
  refine (Finset.sum_le_card_nsmul _ _ B fun (i : Fin (Dw.mult b)) _ => key b (i : Fin (Dw.mult b)) i.2).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  have : Dw.mult b ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
  exact_mod_cast this

theorem collect {f r q L b X x Om w lam sc rd : ℝ} (hf : 8 ≤ f) (hr : 1 ≤ r) (hq0 : 0 ≤ q) (hq : q ≤ r) (hL : 10 ≤ L)
    (hLx : L ≤ x) (hb : 1 ≤ b) (hZ : f * r * L ≤ X) (hOm : |Om| ≤ 3 * L) (hw0 : 0 ≤ w) (hw : w ≤ 10 * (f * r) * b)
    (h1 : lam ≤ ((1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L)) * w)
    (h2 : sc ≤ 250 * f ^ 2 * r ^ 2 * (2 * L)) (h3 : rd ≤ 217 * (f * r * L) ^ 2) :
    2 * lam + 2 * sc + rd ≤ x ^ 4 * X ^ 2 * b := by
  have hfr : 1 ≤ f * r := by nlinarith
  have hZ0 : L ≤ f * r * L := by nlinarith
  have hfrX : f * r ≤ X := by nlinarith
  have hX : 1 ≤ X := hfr.trans hfrX
  have a1 : (2 * q + 1) * (6 * f + 48) ≤ (3 * r) * (12 * f) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have a2 : (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 72 * (f * r * L) := by nlinarith
  have a3 : (1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 76 * X := by linarith
  have a4 : w ≤ 10 * X * b := hw.trans (by gcongr)
  have a5 : lam ≤ 76 * X * (10 * X * b) := h1.trans (mul_le_mul a3 a4 hw0 (by positivity))
  have a6 : (f * r * L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hZ 2
  have a7 : (f * r) * (f * r * L) ≤ X * X := mul_le_mul hfrX hZ (by linarith) (by linarith)
  have a8 : X ^ 2 ≤ X ^ 2 * b := le_mul_of_one_le_right (by positivity) hb
  have a9 : (10 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (hL.trans hLx) 4
  have a10 : 10 ^ 4 * (X ^ 2 * b) ≤ x ^ 4 * (X ^ 2 * b) := mul_le_mul_of_nonneg_right a9 (by positivity)
  have a11 : 0 ≤ X ^ 2 * b := by positivity
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem ne_bot_of_form {K K' R W : Type} [Field K] [NumberField K] [Field K'] [AddCommGroup R] [Module K R] [AddCommGroup W]
    [Module K W] [Module K' W] {C C' : Submodule K R} (hC : C' = C) [Module (𝓞 K) C'] {M : Submodule (𝓞 K) C'}
    (hs : Submodule.span K (M : Set C') = ⊤) {WK : Submodule K W} (e : C ≃ₗ[K] WK) {n : ℕ} {b : Fin n → W} (hb : ∀ k, b k ∈ WK)
    (hsp : Submodule.span K' (Set.range b) = ⊤) {y : W} (hy : y ≠ 0) : M ≠ ⊥ := by
  subst hC
  rintro rfl
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at hs
  have h3 : ∀ k, b k = 0 := fun k => by
    have h1 : e.symm ⟨b k, hb k⟩ ∈ (⊥ : Submodule K C') := by rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg Subtype.val h1
  have h4 : Submodule.span K' (Set.range b) ≤ ⊥ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h3 k)
  exact hy (h4 (by rw [hsp]; exact Submodule.mem_top))

set_option maxHeartbeats 1000000 in

theorem latW_ne_bot (h : GramAt p i) : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
  obtain ⟨-, -, hg, -, -, hs⟩ := h
  obtain ⟨y, -, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hg
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := p.fw.ks i
  exact ne_bot_of_form (cuspW_wtZ _ _) hs (p.fw.e i) hb hsp hy

end GlobalTheory.CovTop.LamCore

end
