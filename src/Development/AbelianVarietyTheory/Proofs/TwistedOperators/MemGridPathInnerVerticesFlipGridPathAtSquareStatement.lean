import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath
