import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaTransformTheta

theorem isThetaFunO_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco φ hφ
  exact
    { quasi := fun γ w => _root_.GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ γ w
      level := _root_.GlobalTheory.ThetaLevel.thetaTr_level D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      cont := _root_.GlobalTheory.ThetaTrCont.continuous_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      smooth := fun k L hL hfin w => _root_.GlobalTheory.ThetaSmooth.contDiff_thetaTr_real D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ k L hL hfin w }

end GlobalTheory.ThetaTransformTheta

end
