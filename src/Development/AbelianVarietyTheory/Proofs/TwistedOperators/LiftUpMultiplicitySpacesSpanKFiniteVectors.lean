import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.EvenOnto.LiftUp

theorem liftUp_stage_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  intro hDS hHC hCD hCW D c k s s' ω f hc hk hs _hs' hp
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hIn : Inputs D X := _root_.GlobalTheory.PairLift.inputs_of_chosenSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (_root_.GlobalTheory.PairLift.cuspAll_of_lowAll D X hIn (_root_.GlobalTheory.PairLift.lowAll_of_lowFock D X hIn (_root_.GlobalTheory.LowerMembersRule.lowFock D X hIn)))
  have hW := hp.weil
  have hstd : IsStdChar D c.ψ (-1) := hW.std
  have hadj : AdjLaw c.ψ s.V s'.V := _root_.GlobalTheory.AdjLawPf.adjLaw D c.ψ hstd s.V s'.V
  have h0 : adjO s.V s'.V 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := _root_.GlobalTheory.WeilConj.exists_conj_weilDatum D c.ψ s.V s'.V (c.χ k) (c.χ k) ω hW
  obtain ⟨j, -, hj⟩ := _root_.GlobalTheory.FockAdjoint.fock_dag D c.ψ c.θ hstd hc.inf s.V s'.V (Fr.ofModel s.M) (Fr.ofModel s'.M)
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hp.vac)
  have hω'e : IsWeilExp c.ψ s'.V s.V (c.a k) (c.a k) ω' :=
    ⟨c.χ k, c.χ k, hW', fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  have hne : dag s.V s'.V f ≠ 0 := by
    intro hz
    apply hp.vac.ne
    funext x
    have hx := congrFun hz (adjO s'.V s.V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec c.ψ c.θ s'.M s.M (dag s.V s'.V f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := (_root_.GlobalTheory.EvenOnto.upPair_itW hDS hHC D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf hp.par).2
  have hItW := hIt ω' (dag s.V s'.V f) hω'e hf'
  have hrule : ∀ τ, RulePar X (s'.par τ) (s.par τ) (c.a k τ) (c.a k τ) :=
    fun τ => ((_root_.GlobalTheory.EvenOnto.upPair_arch hDS hHC D c.t _ _ _ _ (hp.par τ)).2 X h3 h4 h5).2
  have hL := hPL _ _ _ _ hrule s'.V s.V s'.M s.M c.θ c.ψ hc.inf ω' hω'e (dag s.V s'.V f) It hf' hItW s.ν s.fd hs.haar hs.fund
    (dag s.V s'.V f) (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v =>
    _root_.GlobalTheory.ItKFin.itKFin D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf' hItW (j P) v, ?_, ?_⟩
  · refine (GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf'
      hItW).trans (Submodule.span_mono ?_)
    rintro w ⟨P, v, -, rfl⟩
    exact ⟨j.symm P, v, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf c.ψ c.θ s.M s'.M f P)) =
        thetaKO ω' h g (ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P)) := by
      intro g
      have e1 : ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P) = dag s.V s'.V (ptOf c.ψ c.θ s.M s'.M f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.EvenOnto.LiftUp

end
