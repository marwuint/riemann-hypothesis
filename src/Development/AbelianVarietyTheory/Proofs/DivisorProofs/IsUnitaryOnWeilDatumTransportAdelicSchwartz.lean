import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransferHaarFundamentalDomainCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF

theorem isUnitaryOn_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := _root_.GlobalTheory.WeilPairPartnerF.pair_partnerF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := _root_.GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    _root_.GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  rw [hiso _ ht.1, hiso _ hΦ, ht.2, hω.om_unit ν 𝓕 hν h𝓕 _ _ hth]

end GlobalTheory.WeilUnitaryTransportF

end
