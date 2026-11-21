import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Model

variable {D : D7}

def reOm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χS χT om) (π : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (h₁ : ∀ f, IsThetaFunO ψ S T (π f)) (h₂ : ∀ f, IsThetaFunO ψ S T f → π f = f) : Om S T where
  toFun p := (om p) ∘ₗ π + (LinearMap.id - π)
  map_one' := by ext f w; simp
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have e1 : π (om q (π f)) = om q (π f) := h₂ _ (h.om_pres q _ (h₁ f))
    have e2 : π (π f) = π f := h₂ _ (h₁ f)
    simp [map_mul, e1, e2]

theorem reOm_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χS χT om) (π : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (h₁ h₂) (p f) :
    reOm h π h₁ h₂ p f = om p (π f) + (f - π f) := rfl

abbrev nLine (D : D7) : HSp D := GlobalTheory.Doubling.hneg (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)

theorem isLineVec_nLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (nLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  have h : ∀ i j : Fin 1, (nLine D).gram i j = -1 := fun i j => by
    show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
    rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
    simp [Examples₂.sgn]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, (nLine D).gram i j * c ≠ 0
  simp [h, hc]

open GlobalTheory.ChainOnto (Com PiLocalization₂)

end GlobalTheory.SeeSaw.Model

end
