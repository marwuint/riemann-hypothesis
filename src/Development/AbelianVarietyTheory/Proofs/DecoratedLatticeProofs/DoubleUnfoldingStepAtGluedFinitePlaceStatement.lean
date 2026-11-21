import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place : ∀ D : D7, GlobalTheory.FinPl.VertexGlued D := by
  exact @GlobalTheory.FinPl.Vertex.vertexGlued
