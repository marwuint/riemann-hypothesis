import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockS_fockColumnSubstitution_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ) (P Q : GlobalTheory.MinorFrame.Pol ι d a),
  Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
    (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  exact @GlobalTheory.MinorFrame.fockS_colSub_unitary
