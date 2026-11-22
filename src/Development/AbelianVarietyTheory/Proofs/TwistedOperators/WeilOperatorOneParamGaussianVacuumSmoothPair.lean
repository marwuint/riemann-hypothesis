import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLinePairOperatorsOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumIsFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussLinePair

theorem smooth_vacuum_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := _root_.GlobalTheory.LineGroupPair.archOp_oneParam_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := _root_.GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := _root_.GlobalTheory.ArchLineAct.intertwine_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := _root_.GlobalTheory.ArchLineContPair.continuous_apply F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := _root_.GlobalTheory.FockPair.exists_fock_cx F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := _root_.GlobalTheory.WeilVacuum.smooth_flow (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := _root_.GlobalTheory.PolMul.pol_mul_pairInf_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLinePair

end
