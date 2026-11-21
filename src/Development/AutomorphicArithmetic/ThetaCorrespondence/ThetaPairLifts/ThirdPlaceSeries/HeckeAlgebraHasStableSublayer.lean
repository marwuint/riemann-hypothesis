import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeSbLayer
end GlobalTheory.HeckeSbLayer
namespace GlobalTheory.HeckeSbLayer
theorem exists_hecke_stable_sublayer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := by
  intro _ _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c ⟨e⟩ _ _
  have hS0b : ∀ i, ∀ Q ∈ t.r.z.R.Sb, Q ∈ (w.st Z).toD7.ntw.S0 i := by
    intro i P hP
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.st Z).toD7.ntw.placesOver_subset_exceptional i k hk
  have hne : Nonempty (w.st Z).toD7.ntw.Tw := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 (w.st Z).toD7.what₂.LL)
    exact ⟨nch.twI ((w.st Z).toD7.plEq.symm
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩)⟩
  exact exists_sb_raw (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk c.row.nexp c.row.hecke e.hecke e.fi hne
    (fun i P P' hP hc => e.ser.ex.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => e.ser.ex.good.goodSetup_placesOverTwo_subset i) hS0b
end GlobalTheory.HeckeSbLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_superset_low_heckeRd_of_subset_S0 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := by
  exact @_root_.GlobalTheory.HeckeSbLayer.exists_hecke_stable_sublayer_alt
end
end
