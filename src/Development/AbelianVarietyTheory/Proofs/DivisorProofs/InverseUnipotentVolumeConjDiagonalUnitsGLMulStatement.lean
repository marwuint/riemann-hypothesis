import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d e : n ⊕ Fin c → kˣ), invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) * invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  exact @GlobalTheory.FunObj.invVol_conj_diagGL_mul
