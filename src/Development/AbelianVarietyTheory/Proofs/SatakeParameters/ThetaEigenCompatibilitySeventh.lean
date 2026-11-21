import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityNinth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEqStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StrInert

theorem not_isSplitPl_of_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : ¬ IsSplitPl D.host w := by
  rw [GlobalTheory.ConjPlaceOff.isSplitPl_iff]
  rintro ⟨x, hx, hcx⟩
  apply hcx
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin] at hx ⊢
  have key : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal ≤
      (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal).comap
        (Formalism.HermitianLattices.Ext.L3.conjO D.host.E) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : Formalism.HermitianLattices.Ext.L3.conjO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) =
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      apply RingOfIntegers.ext
      rw [Formalism.HermitianLattices.Ext.L3.conjO_coe]
      have : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [this]
      exact Formalism.IndefR.Eqv.star_algebraMapF D _
    rw [e]
    exact Ideal.mem_map_of_mem _ ha
  exact key hx

theorem not_mem_badPl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : GlobalTheory.Hk3.Good R t w)
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) :
    w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  intro h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl, Finset.mem_image, Finset.mem_union] at h
  obtain ⟨PP, hPP, he⟩ := h
  have hne := (hw PP hPP).1
  apply hne
  unfold Formalism.UG.IsInertAt at hin
  have hle : w.asIdeal ≤ PP.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap]
    intro a ha
    have : (PP.under (𝓞 D.host.F)).asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
    rw [← this, he]
    exact ha
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le PP.isPrime.ne_top hle)).symm

end GlobalTheory.StrInert

