import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProducts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

structure Kept : Prop where
  ker : ∀ j, j < D.R.m → ∀ φ ∈ Fm D u j ⊓ W j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ W (j + 1)
  ff : ∀ j, j + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u j ⊓ W j, ffStar D u j ε φ ∈ W j

variable {W}

end GlobalTheory.SeeSawCompare

end
