import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (_root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := _root_.GlobalTheory.WMove.main D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := _root_.GlobalTheory.MixUnip.mixS_unip D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => _root_.GlobalTheory.LeviOrigin.value_at_origin D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    rw [(hmv x).1 h, _root_.GlobalTheory.ValueAtOrigin.mixS_zero_target D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h _ (hth _ f hf), ← hbr]
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    rw [e, (hlv _).1 g, ← hbr]
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    rw [e, (hlv _).2.2 a, ← hbr]
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
