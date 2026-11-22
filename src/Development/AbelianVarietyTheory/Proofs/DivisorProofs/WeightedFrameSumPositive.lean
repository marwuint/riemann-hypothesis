import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruence
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupModel

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_nonneg₀ {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact_eq {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem epStar_eq_epsLev (d M : ℕ) (w M' k0 : ℝ) (hk : M' * k0 = 2 * (M : ℝ) * Real.sqrt d) :
    epStar M' (fdeg E) w k0 = epsLev E d M w := by
  unfold epsLev epStar
  congr 2
  rw [show M' * ((fdeg E : ℝ) * w + 2) * k0 * Real.log 2 = (M' * k0) * ((fdeg E : ℝ) * w + 2) * Real.log 2 by ring, hk]
  ring

theorem comp_bound {r : ℕ} (hr : 0 < r) (X : Data E r) (Xx : DataX E r) (hX : Xx.toData = X) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (w : ℝ) (hw0 : 0 < w) (hw : (∑ τ, X.spread la τ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, X.χ la γ = 1) (d M : ℕ)
    (hL : ∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ Xx.L') (M' : ℝ) (hM' : 0 < M')
    (hk : M' * Xx.k0 = 2 * (M : ℝ) * Real.sqrt d)
    (hT : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ,
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M' : ℂ) * τ.1 b))
    (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) (ho : IsOrth X x0) (hF : IsFundSet X x0 FF) :
    ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epsLev E d M w)) *
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (X.dom.piecewise P 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0) := by
  subst hX
  intro y hy
  have h := _root_.GlobalTheory.supLoc_component E r Xx la P M' w x0 FF hr hP hM' hw hw0 hL
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) ho hF y hy
  rw [epStar_eq_epsLev d M w M' Xx.k0 hk] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  have hae : ∀ᵐ z ∂(muF Xx.toData x0), z ∈ OmF Xx.toData x0 := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF Xx.toData x0)), z ∈ OmF Xx.toData x0 :=
      ae_restrict_mem (ExF.isOpen_OmF Xx.toData x0).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  rw [pnorm_piecewise_eq Xx.toData la P hz]

end GlobalTheory.SupModel

