import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.FirstFacts

theorem pair_of_over (D : D7) {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (P P' : PlE D.host) (hc : IsConjPl D.host P P') (hne : P ≠ P') :
    P ∈ Set.range Pq ↔ P' ∉ Set.range Pq := by
  have e := (GlobalTheory.PlacePair.comap_eq_iff D P P').2 (Or.inr hc)
  constructor
  · rintro ⟨v, rfl⟩ ⟨v', rfl⟩
    obtain rfl : v = v' := HeightOneSpectrum.ext ((hPq v).symm.trans (e.trans (hPq v')))
    exact hne rfl
  · intro h
    let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e1 | e1
    · exact ⟨v, e1.symm⟩
    · exact absurd ⟨v, GlobalTheory.GalChar.isConjPl_unique e1 hc⟩ h

theorem vstd_of_over {K : GlobalTheory.Mem.Top.Ctx} (X : GlobalTheory.Mem.Stages) (hX : K.Over X.B.toPre) (i : Fin X.toD7.R.m) :
    FWT.VStd X.toD7 i := by
  obtain ⟨-, -, -, -, -, hVf, -⟩ := GlobalTheory.Mem.HostFrames.frames_of_over K X hX
  obtain ⟨h1, h2⟩ := hVf i
  rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
  refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
  · rw [HSpace.gram, h1, Matrix.one_apply]
  · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
    refine forall_congr' fun a => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; exact y.2
    · intro h
      exact ⟨⟨x a, h⟩, rfl⟩

theorem mem_range_of_mem_QE {X : Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {Q : HeightOneSpectrum (𝓞 X.E)} : ∀ {ξ}, Q ∈ Col.QE sel ξ → Q ∈ Set.range sel := by
  classical
  intro ξ h
  unfold Col.QE at h
  split_ifs at h
  · obtain ⟨v, -, e⟩ := Finset.mem_image.1 h
    exact ⟨v, e⟩
  · exact absurd h (Finset.notMem_empty _)

end GlobalTheory.HeightCounting.FirstFacts

end
