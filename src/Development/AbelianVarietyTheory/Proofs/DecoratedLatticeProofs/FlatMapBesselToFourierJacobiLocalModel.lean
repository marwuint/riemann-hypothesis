import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFreeEntryTranslationLawsBesselToJaco
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFlatMapLocalUnipotentTranslationLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplication

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatBFLoc

theorem flatBF_of_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW hco hbe hja Tm hTm
  obtain ⟨hcont, hne⟩ := (_root_.GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std).2.1 ψk hψk
  have hc : c = 2 * ρ := by have := hbe.1; omega
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ) :=
    { toFun := fun Φ => flatBF st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add]
        exact (_root_.GlobalTheory.FlatLin.flatBF_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ') 1 (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (_root_.GlobalTheory.FlatLin.flatBF_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ) a (hTm.theta Φ) (hTm.theta Φ)).2 }
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.FlatFactor.flCol_factor k ψk ν hcont hne hν n n' c ρ (WO B.V₀ J.W₀ → ℂ) L hc
    (_root_.GlobalTheory.FlatColLaw.law_dual_col D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatRow.flatBF_mul_row D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatTransLaw.flatBF_trans D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatUnip.flatBF_unip D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
  have hL : ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ := hL₀
  refine ⟨L₀, ⟨?_, ?_, ?_⟩, hL⟩
  · exact _root_.GlobalTheory.LocModTheta.flat_model_theta D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact _root_.GlobalTheory.FlatTrans.factor_trans D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact _root_.GlobalTheory.FlatBFLoc.ModelModul.model_modul D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL

end GlobalTheory.FlatBFLoc
end
