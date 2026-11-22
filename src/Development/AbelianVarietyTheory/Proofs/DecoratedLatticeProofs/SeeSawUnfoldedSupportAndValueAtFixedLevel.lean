import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawLaws

open GlobalTheory.LocMod

theorem gsupp2_all (D : D7) : GlobalTheory.LocMod.GSupp2 D := by
  have hFL : FlatLaw D := _root_.GlobalTheory.Unf.Flat.flatLaw D
  have hFLs : GlobalTheory.FinPl.FlatLaws D := _root_.GlobalTheory.FinPl.flatLaws_all D
  have hOm : OmLoc D := _root_.GlobalTheory.LocOm.omLoc D
  have hBF : FlatBF D := _root_.GlobalTheory.FlatBFLoc.flatBF_of_laws D hFL hFLs hOm
  have hFB : FlatFB D := _root_.GlobalTheory.LocMod.flatFB_holds D hFL hFLs hOm
  have hC : ContrLoc D := _root_.GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hS : GlobalTheory.LocFlat.SymCollapse := GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds
  intro k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  exact _root_.GlobalTheory.LocMod.GSuppTwo.gsupp2_std D hOm hBF hFB hC hS k p s κ S t ψ s₁.weil.std hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne

theorem gsupp1_all (D : D7) : GlobalTheory.LocMod.GSupp1 D :=
  _root_.GlobalTheory.LocMod.SuppFirst.gsupp1 D (_root_.GlobalTheory.LocOm.omLoc D)
    (_root_.GlobalTheory.FlatBFLoc.flatBF_of_laws D (_root_.GlobalTheory.Unf.Flat.flatLaw D) (_root_.GlobalTheory.FinPl.flatLaws_all D) (_root_.GlobalTheory.LocOm.omLoc D))
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds)

theorem gLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  obtain ⟨a, ha, hval⟩ := GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel D c v n G hc hv hG
  refine ⟨a, ha, fun t ht hW hch => ⟨?_, hval t ht hW⟩⟩
  have hs : GSupp (t := t) v :=
    GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces D c v n G hc hv hG (gsupp1_all D) (gsupp2_all D) (_root_.GlobalTheory.Unf.Flat.flatLaw D) t ht hch
  exact hs

end GlobalTheory.SeeSawLaws
