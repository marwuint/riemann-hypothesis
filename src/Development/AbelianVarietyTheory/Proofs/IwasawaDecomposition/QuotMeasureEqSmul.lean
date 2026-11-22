import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

end GlobalTheory.ReadingNorm
