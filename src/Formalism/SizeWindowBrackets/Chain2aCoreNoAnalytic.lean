import Formalism.SizeWindowBrackets.SChain
import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.GaloisToProductIsIso
import Formalism.SizeWindowBrackets.WindowSettingSatisfiable

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

instance decFinPl (K : Type) [Field K] [NumberField K] : DecidableEq (slopeLatticeData.FinPl K) := Classical.decEq _

section Places
variable {K : Type} [Field K] [NumberField K]

def prBelow (w : slopeLatticeData.FinPl K) : ℕ := Ideal.absNorm (w.1.under ℤ)

def ramE (w : slopeLatticeData.FinPl K) : ℝ := (w.1.ramificationIdx ℤ : ℝ)

def lE (w : slopeLatticeData.FinPl K) : ℝ := slopeLatticeData.ell w * ramE w

end Places

structure Fam (I : Type) (m : ℕ) where

  K : Type
  [indexKFirst : Field K]
  [indexKSecond : NumberField K]
  [indexKThird : StarRing K]
  [indexKFourth : IsTotallyComplex K]

  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]

  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]

  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  ι : I → Type
  [indexCFirst : ∀ i, Fintype (ι i)]
  [indexCSecond : ∀ i, DecidableEq (ι i)]

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  ιf : I → Type
  [indexDFirst : ∀ i, Fintype (ιf i)]
  [indexDSecond : ∀ i, DecidableEq (ιf i)]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (ι i) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (ιf i) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (ιf i) (ιf i) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K
  Y : ∀ i, Matrix (ι i) (ι i) ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ
  γ : I → ℝ
  Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ
  Vr : ∀ i, Matrix (ιf i) (ι i) ℂ

  S : Finset (slopeLatticeData.FinPl K)
  gain : Fin m → slopeLatticeData.FinPl K → ℝ
  Fj : Fin m → slopeLatticeData.FinPl K → ℝ
  Ej : I → Fin m → slopeLatticeData.FinPl K → ℝ

  iop : ℕ → ℝ

  T : I → ℕ

  h : I → ℝ

  lam : I → ℝ
  Dstar : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] Fam.indexKFirst Fam.indexKSecond Fam.indexKThird Fam.indexKFourth Fam.indexWFirst Fam.indexWSecond Fam.indexWThird Fam.indexWFourth Fam.firstRealIndex Fam.secondRealIndex Fam.firstRationalIndex Fam.secondRationalIndex
  Fam.indexVFirst Fam.indexVSecond Fam.indexVThird Fam.indexVFourth Fam.indexCFirst Fam.indexCSecond Fam.indexFFirst Fam.indexFSecond Fam.indexFThird Fam.indexFFourth Fam.indexDFirst Fam.indexDSecond

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

def N' (u : I) : Submodule (𝓞 F.K) (F.V u) := slopeLatticeData.modLat (F.σ u) (F.N0 u)

def ItM (u : I) : Submodule (𝓞 F.K) (F.V u) :=
  Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow F.τ : FractionalIdeal (nonZeroDivisors (𝓞 F.K)) F.K) :
    Submodule (𝓞 F.K) F.K) (F.M u)

def du (u : I) : ℝ := (Fintype.card (F.ι u) : ℝ)

def dM (u : I) : ℝ := (Fintype.card (F.ιf u) : ℝ)

def tauR (w : slopeLatticeData.FinPl F.K) : ℝ := (F.τ w : ℝ) / ramE w

def sgR (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := (F.σ u w : ℝ) / ramE w

def lenN (u : I) (w : slopeLatticeData.FinPl F.K) : ℕ := (slopeLatticeData.lenAt w (F.ItM u) (F.N0 u)).toNat

def lenR (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := ((F.lenN u w : ℝ) + F.du u * (F.τ w : ℝ)) / ramE w

def sgw (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := UnitWeightPartition.sgw Finset.univ F.gain F.Fj (F.Ej u) w

def ST (u : I) : Finset (slopeLatticeData.FinPl F.K) := F.S.filter (fun w => prBelow w = F.T u)

def Pr : Finset ℕ := F.S.image prBelow

def EeJ (u : I) (j : Fin m) : ℝ := 2 * ∑ w ∈ F.S, lE w * F.Ej u j w

def Rd (u : I) : ℝ := ∑ w ∈ F.S, 2 * lE w * (F.sgw u w - F.sgR u w)

end Fam

structure Glob where

  x : ℝ

  ε : ℝ

  k : ℝ

  La : ℝ

  v : ℝ

  lg : ℝ

  delBar : ℝ

  etaBar : ℝ

  eBar : ℝ

end Formalism.LFunctionChainParameters.LChain2
