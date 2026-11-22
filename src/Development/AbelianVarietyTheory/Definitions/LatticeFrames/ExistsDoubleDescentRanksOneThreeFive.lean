import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonarchimedeanLocalFieldSecondCountableT2Space
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def sph (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n]
    [DecidableEq n] : Level (GL n k) := ⟨KO k n, 1⟩

theorem exists_haar (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ m : Measure (GL n k), m.IsHaarMeasure ∧ m (KO k n) = 1 := by
  obtain ⟨h0, _, _, h1, h2, -⟩ := volGL_haar k n ν
  haveI : BorelSpace (GL n k) := h0
  haveI := (GlobalTheory.RootExchangeFixed.nonarchimedeanLocalField_secondCountable_t2Space (k := k)).2
  let K : TopologicalSpace.PositiveCompacts (GL n k) := ⟨⟨KO k n, h1⟩, by rw [h2.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

end Local

variable {D : D7}

theorem exists_gl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    ∃ gl : GL Y k →* GA D V, ∀ g, (ofSplit q).IsLoc F (gl g) g :=
  let ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V Y F.β F.γ F.βγ F.γβ
  ⟨gl, fun g => ⟨h1 g, h2 g⟩⟩

end GlobalTheory.QPl.Model
end
