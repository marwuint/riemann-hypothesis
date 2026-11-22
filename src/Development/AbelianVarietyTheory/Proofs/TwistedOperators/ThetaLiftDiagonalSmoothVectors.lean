import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Size

variable {D : D7}

theorem thetaKO_le_unif {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    {K : Set (GA D W)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h f‖ ≤ C * GlobalTheory.Grow.height V g ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact W hK
  have hs : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A, A, mul_nonneg hs (pow_nonneg (by positivity) _),
    fun h hh g => ?_⟩
  have h1 := (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h
  have hW : GlobalTheory.Grow.height W h ≤ max B 1 := (hB h hh).trans (le_max_left _ _)
  have hW0 : 0 ≤ GlobalTheory.Grow.height W h := (GlobalTheory.Grow.height_pos W h).le
  have hV0 : 0 ≤ GlobalTheory.Grow.height V g := (GlobalTheory.Grow.height_pos V g).le
  calc ‖thetaKO ω g h f‖ = ‖ω (g, h) f 0‖ := rfl
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := h1
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * max B 1) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hV0 hW0)
          (mul_le_mul_of_nonneg_left hW hV0) _) hs
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A * GlobalTheory.Grow.height V g ^ A := by ring

theorem thetaKO_le_quotHeight {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε S) T Φ) {K : Set (GA D T)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.quotHeight S g ^ A := by
  have e : ∀ g h, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((GlobalTheory.Grid.ofSgn ε S).symm g) h Φ := fun g h => by
    show ω (g, h) Φ 0 = ω (GlobalTheory.Grid.ofSgn ε S ((GlobalTheory.Grid.ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  obtain ⟨C, A, hC0, hC⟩ := thetaKO_le_unif hθ hω hΦ hK
  have hC' : ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.height S g ^ A := fun h hh g => by
    simp only [e]
    exact hC h hh _
  exact ⟨C * 2 ^ A, A, by positivity, fun h hh g => GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) (hC' h hh) g⟩

end GlobalTheory.DownApprox
