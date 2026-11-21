import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawIdentityWeilTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaAgreeConv

theorem map_finRel_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D}
    {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁} {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'}
    (hM : GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') {Ψ}
    (hΨ : Ψ ∈ GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B)) : p' Ψ = 0 := by
  have hle : GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B) ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    show p' (ωB (u, 1) Ψ - Ψ) = 0
    rw [map_sub, hM.mapB.invf u hu Ψ hΨ, sub_self]
  exact hle hΨ

section Reg

open MeasureTheory GlobalTheory.SquareComm GlobalTheory.RegCompare

variable {D : D7}

theorem intg_right {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (k : GA D M) :
    Intg ω ν 𝓕 (ω (k, 1) Φ) ∧ thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  have key := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hΦ h) k
  refine ⟨fun h => ?_, ?_⟩
  · simpa only [thetaKO_right] using (key h).1
  · funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h).2

theorem thetaInt_wop_of_intg {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) :
    thetaInt ω ν 𝓕 (wop ω z Φ) = GlobalTheory.FunObj.zdeg z • thetaInt ω ν 𝓕 Φ := by
  have hk := fun k => intg_right hν hL hΦ k
  rw [wop_apply, thetaInt_sum _ fun k _ => ((hk k).1).smul _]
  simp only [thetaInt_smul, (hk _).2, GlobalTheory.FunObj.zdeg, Finsupp.sum, Finset.sum_smul]

end Reg

end GlobalTheory.ThetaAgreeConv
