import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.WeilBound.CoreStatements.AutomorphicKernels.TemperedUnitNorm.NormEqOneOfTemperedRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRep
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
include hF C in
theorem cuspFam_alt_alt (hG : _root_.UpperTheory.GalS.CuspUAlt) {l : ℕ} [hp : Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    CuspFam D.naut ι := by
  intro a ha π hc s hs
  have := host_isCMField D.host
  obtain ⟨r, h1, h3⟩ := _root_.GlobalTheory.HeightCounting.Blocks.exists_rep_alt_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) s fun τ => by
    have := hs τ
    rwa [C.inf] at this
  have hfin : ∀ᶠ w : PlE D.host in cofinite, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by simpa using hp.out.ne_zero
    exact ((Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv).eventually_cofinite_notMem
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub h1).matrix_det
  · filter_upwards [hfin, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ z
    have hu' := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
    have e : T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
      have hu2 := (T.unr w _).1 hu'
      rw [← D.naut.lpTw_add, T.tw, T.tw, C.loc] at hu2 ⊢
      exact ((h3 w hl _ _).eq_unr hu2).symm
    rw [galPol, T.frobEig w _ hu', e, ← frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ]
    exact (eval_map_apply ι.toRingHom _).symm
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
namespace GlobalTheory.GalAllPlaces
end GlobalTheory.GalAllPlaces
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
