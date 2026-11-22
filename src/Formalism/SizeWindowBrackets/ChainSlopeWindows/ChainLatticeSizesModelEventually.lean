import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SlopeInequalityOfLattices
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
import Formalism.SizeWindowBrackets.JointDPublishedSizes

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

def prim (u : I) : LatticeToWeightTransfer.PPrim (slopeLatticeData.FinPl F.K) m where
  S := F.S
  ST := F.ST u
  l := lE
  gain := F.gain
  F := F.Fj
  E := F.Ej u
  tau := F.tauR
  io := fun w => F.iop (prBelow w)
  len := F.lenR u
  sg' := F.sgR u
  dM := F.dM u
  du := F.du u
  muMu := muDef (F.b u) (F.X u) (F.M u)
  muMaxMu := muMaxDef (F.b u) (F.X u) (F.M u)
  Rd := F.Rd u
  lam := F.lam u
  Pr := F.Pr
  pr := prBelow
  iop := F.iop

end Fam

section ModelLemmas

open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

open Classical in

def plOver (p : ℕ) : Finset (slopeLatticeData.FinPl K) :=
  if h : {w : slopeLatticeData.FinPl K | prBelow w = p}.Finite then h.toFinset else ∅

def tau0 (p₁ t₁ : ℕ) : slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.onFinset (plOver K p₁)
    (fun w => if w ∈ plOver K p₁ then ((w.1.ramificationIdx ℤ : ℕ) : ℤ) * (t₁ : ℤ) else 0)
    (fun w hw => by
      by_contra h
      exact hw (if_neg h))

variable {K} in
theorem twist_vector_apply (p₁ t₁ : ℕ) (w : slopeLatticeData.FinPl K) :
    tau0 K p₁ t₁ w = if w ∈ plOver K p₁ then ((w.1.ramificationIdx ℤ : ℕ) : ℤ) * (t₁ : ℤ) else 0 := rfl

end ModelLemmas

open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

end Formalism.LFunctionChainParameters.LChain2
