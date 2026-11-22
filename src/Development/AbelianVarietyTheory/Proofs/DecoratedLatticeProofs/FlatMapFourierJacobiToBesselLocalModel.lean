import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSource
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFourierJacobiToBesselColumnMulLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapRowMultiplication
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapTranslationLawsJacobiToBesselFree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapUnipotentLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocMod

theorem flatFB_holds : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  obtain ⟨hcont, hne⟩ := (_root_.GlobalTheory.LocChar.weil_char_split D k p ψ hstd).2.1 ψk hχ
  have hc : c = 2 * σ + 1 := hBF.1
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ) :=
    { toFun := fun Φ => flatFB st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add]
        exact (_root_.GlobalTheory.FlatAdd.flatFB_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (_root_.GlobalTheory.FlatAdd.flatFB_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ)).2 a }
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.PartRed.flRow_factor k ψk ν hcont hne hν n n' c σ (WO J.W₀ B.V₀ → ℂ) L hc
    (_root_.GlobalTheory.FlatColLawFB.flatFB_mulcol D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.LocMod.flatFB_mulrow D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.LocMod.flatFB_trans_free D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.FlatFBUnip.unip_law D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
  exact ⟨L₀, _root_.GlobalTheory.LocFlatFB.factor_isModel D hFLs hOm k p ν hν ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm L₀ hL₀, hL₀⟩

end GlobalTheory.LocMod

end
