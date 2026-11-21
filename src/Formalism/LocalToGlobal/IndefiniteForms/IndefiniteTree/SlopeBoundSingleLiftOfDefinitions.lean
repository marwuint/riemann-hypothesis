import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet

open Finset Module NumberField Formalism.HN

noncomputable section

namespace Formalism.L2.Indef.Tree

structure SlopeBoundParameters where

  Pl : Type

  fPl : Fintype Pl

  x : ℝ

  eps : ℝ

  rd : ℝ

  v : ℝ

  dN : ℕ

  dimNeZero : NeZero dN

  χ : DirichletCharacter ℂ dN

  Z : ℝ

  logOmK : ℝ

  logOm : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  S : ℝ

  η : ℝ

  R : ℝ

  PPp : ℝ

  PPpp : ℝ

  PP : ℝ

  PPT : ℝ

  Zpg : ℝ

  nV : ℝ

  Nr : ℝ

  g12 : ℝ

attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero

def LcOf {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def leadingConstant {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0).re

def eulerConstantTerm (n : ℕ) : ℝ :=
  (∑ q ∈ reducedForms (-(n : ℤ)), Real.log (4 * Real.pi * (formRoot (-(n : ℤ)) q).im *
    ‖ModularForm.eta (formRoot (-(n : ℤ)) q)‖ ^ 4)) / ((reducedForms (-(n : ℤ))).card : ℝ)

namespace SlopeBoundParameters

variable (P : SlopeBoundParameters)

def L : ℝ := P.x ^ P.eps

def b : ℝ := Real.exp P.L

def lrd : ℝ := Real.log P.rd

def llx : ℝ := Real.log (Real.log P.x)

def dK : ℝ := (P.dN : ℝ)

def Lc : ℝ := LcOf P.χ

def L0 : ℝ := leadingConstant P.χ

def A1 : ℝ := eulerConstantTerm P.dN

def LL0 : ℝ := Real.log (P.b * P.rd) * P.llx + |P.Lc| + Real.log P.x

end SlopeBoundParameters

structure SlopeBoundLiftData (K : Type) [Field K] [NumberField K] [StarRing K] (P : SlopeBoundParameters) where

  w : P.Pl → ℝ

  w0 : P.Pl → ℝ

  c1 : P.Pl → ℝ

  ua : P.Pl → ℝ

  kap : ℝ

  q' : ℕ

  pq : ℝ

  ι : Type

  fι : Fintype ι

  nι : Nonempty ι

  DY : ℝ

  A : ℝ

  cs : ℝ

  X : ℝ

  cc : ℝ

  E0 : ℝ

  Qcc : ℝ

  ρ : ℝ

  R1 : ℝ

  R2 : ℝ

  Bn : ℝ

  δ' : ℝ

  h : ι → ℝ

  sl : ι → ℝ

  δc : ι → ℝ

  dc : ι → ℝ

  degc : ι → ℝ

  PPf : ℝ

  mv : ℝ

  muU : ℝ

  nA : ℕ

  nB : ℕ

  nN : ℕ

  XA : InfinitePlace K → Matrix (Fin nA) (Fin nA) ℂ

  XB : InfinitePlace K → Matrix (Fin nB) (Fin nB) ℂ

  XN : InfinitePlace K → Matrix (Fin nN) (Fin nN) ℂ

  LA : Submodule (𝓞 K) (Fin nA → K)

  LB : Submodule (𝓞 K) (Fin nB → K)

  NN : Submodule (𝓞 K) (Fin nN → K)

  Mk : Submodule (𝓞 K) (Fin nN → K)

  φ : (Fin nA → K) →ₗ[K] (Fin nB → K)

  e : (Fin nN → K) →ₗ[K] (Fin nN → K)

  g : ℕ

  PPh : ℝ

  abelian₂ : ℝ

  δ : ℝ

  o' : ℝ

  n2 : ℝ

attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι

namespace SlopeBoundLiftData

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P)

def T : ℝ := ((⌈P.PPT ^ 2 * F.DY ^ 2 * P.k / P.m⌉ : ℤ) : ℝ)

def U : ℝ := ∑ τ, F.ua τ

def main : ℝ := ∑ σ, F.pq * F.w0 σ * P.logOm

end SlopeBoundLiftData

def LeafDiff (P : SlopeBoundParameters) : Prop :=
  P.logOmK = P.A1

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

def LeafMeans (Ca Cb : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.X ∧ -F.X ≤ (∑ c, F.sl c) / (Fintype.card F.ι : ℝ) ∧
    F.T * F.X ≤ Ca * P.LL0 * (F.U + F.E0) ∧ F.T * F.cc ≤ Cb * P.LL0 * (F.U + F.E0) + F.T * F.Qcc

end Leaves

end Formalism.L2.Indef.Tree
