import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors
