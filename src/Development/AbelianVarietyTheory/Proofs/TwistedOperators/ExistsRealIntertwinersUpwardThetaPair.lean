import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_itW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) →
    (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω →
      GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω →
      GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  intro hDS hHC D t V W S S' M M' aS aT θ ψ hθ hP
  obtain ⟨X, hX, h1, h2, -⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hB := _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd e1 e2
  choose hr A hA using key
  refine ⟨?_, ?_⟩
  · obtain ⟨It, I, hI⟩ := _root_.GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt D V W _ _ M M' aS aT A GlobalTheory.ContrObj.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => _root_.GlobalTheory.VacuumCharacter.vacChar D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI hr (_root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
      fun τ => (hv τ).2.2
  · have hA' : ∀ τ, ∃ A', LocIt M' M τ (aT τ) (aS τ) A' := fun τ =>
      _root_.GlobalTheory.AdjLocIt.adj_locIt D V W _ _ M M' τ _ _ (A τ) (hA τ)
    choose A' hA' using hA'
    obtain ⟨It, I, hI⟩ := _root_.GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt D W V _ _ M' M aT aS A' GlobalTheory.ContrObj.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA'
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => _root_.GlobalTheory.VacuumCharacter.vacChar D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
      (_root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.EvenOnto

end
