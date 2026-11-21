import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFrameUnitaryDivisorSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameInt

theorem exists_split (D : D7) (PP : HeightOneSpectrum (𝓞 D.host.E)) (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP) :
    ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = PP := by
  refine GlobalTheory.RowUnitProof.exists_splitPlace_eq D PP ?_
  by_contra hs
  refine h fun c hc => ?_
  by_contra hn
  exact hs ⟨c, hc, fun y hy hm => hn ⟨y, hm, hy.trans (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩⟩

theorem frame_of {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0)
    (hF : D.host.F = maximalRealSubfield D.host.E) (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV)
    (hP : R3.StdFrame hF P) (s : T) :
    (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (L.βV k)) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (L.βV k) s' φ b := by
  have hβ : IsBaseFrame (Vc D k) (L.βV k) (L.ΛV k) 1 := by
    obtain ⟨c, hc⟩ := hL.βV k
    rwa [one_pow] at hc
  refine ⟨fun κ hκ => ?_, fun PP h => ?_⟩
  · have h1 := (hP.2 κ).1 hκ
    exact (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ h1.1).2 h1
  · have hn : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP :=
      h.elim (fun h => GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hL.Pg PP h PP h) fun h => (hL.Q_pl s PP h).2 PP h
    obtain ⟨s', hs'⟩ := exists_split D PP hn
    obtain ⟨φ, b, h1, h2⟩ := _root_.GlobalTheory.FrameRedSplit.frameRed_exists D (Vc D k) D.R.nV (GlobalTheory.FrameBlockDiagonal.rankV D k) hF P (L.βV k) (L.ΛV k) hP hβ s'
    exact ⟨s', φ, b, hs', h1, h2⟩

end GlobalTheory.FrameInt

end
