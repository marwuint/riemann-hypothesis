import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger

theorem exists_isUWeilPair_hsp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ om, GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
            (incM D.host.F JA) (incM D.host.F JB) co χT χS om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ S T χS χT hψ hS hT rS rT
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.ThetaTransform.exists_isTransport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h3 := _root_.GlobalTheory.WeilAdm.transport_adm D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h4 := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h5 := _root_.GlobalTheory.WeilCont.continuous_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h6 := _root_.GlobalTheory.DblSchr.doubledModel D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h7 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  exact ⟨om, ⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ co, transD_e co, isUSplitting_inl hsp, h7⟩, h5⟩

end GlobalTheory.WeilSchrodinger

end
