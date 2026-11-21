import Formalism.SizeWindowBrackets.ClaimGaFree
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

structure PData (ι : Type) (m : ℕ) where

  S : Finset ι

  ST : Finset ι
  l : ι → ℝ
  gain : Fin m → ι → ℝ
  F : Fin m → ι → ℝ
  E : Fin m → ι → ℝ
  tau : ι → ℝ
  io : ι → ℝ
  len : ι → ℝ
  sg' : ι → ℝ
  dM : ℝ
  du : ℝ
  de : ℝ
  muMu : ℝ
  muMaxMu : ℝ
  PT : ℝ
  Rd : ℝ
  IOp : ℝ
  LT : ℝ
  RX : ℝ

namespace PData

variable {ι : Type} [DecidableEq ι] {m : ℕ} (p : PData ι m)

def Fo : ℝ := UnitWeightPartition.Fo p.S Finset.univ p.l p.F

end PData

structure PPrim (ι : Type) (m : ℕ) where
  S : Finset ι
  ST : Finset ι
  l : ι → ℝ
  gain : Fin m → ι → ℝ
  F : Fin m → ι → ℝ
  E : Fin m → ι → ℝ
  tau : ι → ℝ
  io : ι → ℝ
  len : ι → ℝ
  sg' : ι → ℝ
  dM : ℝ
  du : ℝ
  muMu : ℝ
  muMaxMu : ℝ
  Rd : ℝ
  lam : ℝ
  Pr : Finset ℕ
  pr : ι → ℕ
  iop : ℕ → ℝ

end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
