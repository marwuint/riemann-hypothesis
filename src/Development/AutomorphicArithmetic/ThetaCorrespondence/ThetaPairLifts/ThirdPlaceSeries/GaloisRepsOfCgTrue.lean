import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting
theorem galoisReps_of_cgTrue_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → UpperTheory.GalS.GaloisRepsN D := by
  intro hL hF hG D T C π hc hr l _ ι
  have := host_isCMField D.host
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr' : (C.e _ π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := _root_.UpperTheory.GalS.exists_aw_alt hL hF hG D.nd.Om ι ha (C.e _ π).1 ((C.csd _ π).1 hc) hr'
  refine ⟨r, h1, h2, fun w hw => ?_⟩
  have hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have k : UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))) := by
    rw [T.tw, C.loc]
    exact h3 w hl _ _
  refine ⟨fun hg s hs => ?_, fun hu => ?_, fun hu B s hB hs => ?_⟩
  · rw [T.inePol w _ s hs, inePol_wdOf (h := D.nd.plOm.2 w) hl ι h1 hs, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs,
      k.ine (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (hg.nc T))) _ (deg_ineIncl _)]
  · rw [← weilDeligneParam_monodromy_eq_zero_iff hl ι h1]
    exact k.mono (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (.of_unr hu)))
  · have hu' := (D.naut.unr_tw _ ((1 - (D.R.r : ℝ)) / 2)).2 hu
    have e := (k.eq_unr ((T.unr w _).1 hu')).symm
    rw [galPol, T.frobEig w _ hu', e]
    exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hs
end GlobalTheory.GalAway
end
end
