import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open scoped ContDiff ComplexOrder

namespace GlobalTheory.ColLiftAut

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}

theorem isThetaFunO_smul (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem kernel_left (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ) (g : GA D S) {γ : GA D T}
    (hγ : γ ∈ GQ T) (h : GA D T) : thetaKO om g (γ * h) Φ = thetaKO om g h Φ := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hΦ)

theorem kernel_right (g : GA D S) (h k : GA D T) : thetaKO om g (h * k) Φ = thetaKO om g h (om (1, k) Φ) := by
  have e : ((g, h * k) : GA D S × GA D T) = (g, h) * (1, k) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]

theorem lift_continuous (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    Continuous fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  have := GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector ψ S T χS χT om hW hS ν 𝓕 hν h𝓕 ℂ
    (LinearMap.toSpanSingleton ℂ _ Φ) (fun x => isThetaFunO_smul hΦ x) φ hφ.cont hφ.left
  refine this.congr fun h => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [LinearMap.toSpanSingleton_apply, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end GlobalTheory.ColLiftAut

namespace GlobalTheory.ColLiftAut

theorem posDef_of_nodeIs {D : D7} {N : GlobalTheory.Grid.Node D} {ν q : ℕ} {Sp : D.what₂.Tau → SPar} (h : N.Is ν q Sp) (hq : q = 0) :
    ∀ τ, (gramAt D N.V τ).PosDef := fun τ =>
  GlobalTheory.RepsObj.gramAt_posDef (fun σ => by rw [h.sig σ, h.rank, hq]; simp) h.sigOK τ

end GlobalTheory.ColLiftAut
