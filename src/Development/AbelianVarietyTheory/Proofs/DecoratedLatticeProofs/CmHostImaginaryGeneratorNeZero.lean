import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Inhab

variable {D : D7}

theorem nonempty_vol (V : HSp D) : Nonempty (Vol V) :=
  let ⟨μ, 𝓕, h1, h2⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  ⟨⟨μ, 𝓕, h1, h2⟩⟩

theorem nonempty_volN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem coCpt_of_mul {V : HSp D} (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso {V : HSp D} (h : IsAniso V) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h)

theorem coCpt_of_posDef {V : HSp D} (h : ∀ τ, (gramAt D V τ).PosDef) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)

theorem exists_weil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {χS χT : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χT) (h3 : ResEta D χS S.rank) (h4 : ResEta D χT T.rank) :
    ∃ om, IsWeilDatumO ψ S T χS χT om :=
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) h1 h2 h3 h4

theorem nonempty_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) : Nonempty (Step ψ V V₀ W W₀ ρ σ) := by
  obtain ⟨χV, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨χW, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D W.rank
  obtain ⟨om, h⟩ := exists_weil hψ V W a1 b1 a2 b2
  obtain ⟨om₀, h₀⟩ := exists_weil hψ V₀ W₀ a1 b1 (resEta_parity a2 hV) (resEta_parity b2 hW)
  obtain ⟨vW⟩ := nonempty_vol W
  obtain ⟨vS⟩ := nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩⟩

theorem even_im_hermitian_sub {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : S.rank % 2 = S₀.rank % 2 := by
  have := d.rank_add
  omega

theorem nonempty_stepBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) :
    Nonempty (StepBF ψ B J) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub B.d) (even_im_hermitian_sub J.d)

theorem nonempty_stepFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) : Nonempty (StepFB ψ J B) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub J.d) (even_im_hermitian_sub B.d)

theorem cmHost_imaginaryGenerator_ne_zero (D : D7) : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

end GlobalTheory.Unf.Inhab

end
