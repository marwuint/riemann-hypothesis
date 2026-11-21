import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffS
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferAllFinitePlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (VacFin)

noncomputable section

namespace GlobalTheory.ChainTw

theorem upParQ_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpParQ D := by
  intro hRD hHowe D hND c w hw k hk s s' hs hs' p hp u B φ hu v _ hne
  obtain ⟨hr, _, hfl⟩ := hs
  obtain ⟨hr', _, hfl'⟩ := hs'
  have hlat' : ∀ (f : GA D s'.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s'.V.gram s'.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s'.V c.S f B := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hw.com (k + 1) hk _ hfl').2
  have hlat : ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hw.com k hk.le _ hfl).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by
    have h1 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    have h2 : s.V.rank = D.R.rankY k := hfl.rank
    rw [h1, h2, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hfock := _root_.GlobalTheory.ChainTw.fock_sph_tw D hND c w hw k hk s s' ⟨hr, by assumption, hfl⟩ ⟨hr', by assumption, hfl'⟩ p hp
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w' h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact _root_.GlobalTheory.ChainOnto.thetaIntegral_param hRD D (_root_.GlobalTheory.ChainOnto.transferOn_all hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil D.R.t hrank s.ν s.fd
    hfl.haar hfl.fund w0 (fun w'' hw'' => _root_.GlobalTheory.ChainOnto.step_chars_unrAt D c hw.com k hk w0 hw0' w'' hw'') w' h (p.pt φ)
    ((hfock.1 φ).2.2 w0 hw0') y (B w') hYA.1 hYA.2 (hyB w0 hw0 w' h) hne'

end GlobalTheory.ChainTw

end
