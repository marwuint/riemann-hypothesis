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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.ParLawsBare

open GlobalTheory.RowTie GlobalTheory.NPin Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem heckeCharTie_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) :
    GlobalTheory.HeckeSplitRow.HeckeCharTie D.nd D.naut :=
  ⟨fun π => (cs.e1 π).1, fun _ _ h => cs.e1.injective (Subtype.ext h), cs.unr_iff, cs.frob⟩

theorem heckeSplitOne_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) : GlobalTheory.RowCopy.HeckeSplitOne D :=
  fun ν ν' hw => GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut (heckeCharTie_of_side cs) ν ν' hw

theorem cancel_of_tie {D : D7} (T : WDTie D.nd D.naut) :
    ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := by
  intro w a b c h
  apply (T.e w).injective
  refine GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ (T.e w c) ?_
  rw [← T.sum, ← T.sum, h]

theorem tieAut_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) (hE : IsEmpty D.nd.Loc) :
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := by
  have hcsd : IsCSD D.host cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ cf.isEta
  have hE1 : (cs.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [cs.etaT]; exact cf.isEta.inf⟩
  have hE' : (cs.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.hasInf_inv cf.isEta.inf⟩
  refine ⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i _ => isEmptyElim i⟩
  · rw [cs.csd, cs.etaT]; exact hcsd
  · rw [cs.csd, cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).1, (cs.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).2, (cs.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, cs.frob _ w ((cs.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((cs.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 := (cs.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]

theorem tieGal_bare {D : D7} (hE : IsEmpty D.nd.Loc) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

theorem tieLab_of_lab {D : D7} (T : WDTie D.nd D.naut) (lab : LabTrue D T) : Formalism.MainNotions.SumRepresentations.tieLab D := by
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om :=
    fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, lab k v⟩
  exact GlobalTheory.LabLaws.tieLab_of_labTie hT

end GlobalTheory.ParLawsBare

end
