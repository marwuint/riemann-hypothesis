import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.LeafMeansFree

noncomputable section

open Finset

namespace IxMeans

structure MeansPack (Tau ι : Type) [Fintype Tau] [Fintype ι] where

  N : ℕ

  f : ℕ

  T : ℕ

  D : ℕ

  jp : ℕ

  m : ℕ

  nc : ℕ

  u : Tau → Fin N → ℝ

  u1 : Tau → Fin N → ℝ

  up : Tau → Fin N → ℝ

  c0 : ℝ

  b : ℝ

  rd : ℝ

  x : ℝ

  Lp : ℝ

  h0 : ℝ

  fourthRootConstant : ℝ

  sl : ι → ℝ

  e : ℕ →₀ ℝ

  SB : Finset ℕ

  cpp : ℕ → ℝ

  vdd : ℕ → ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

def C7 : ℝ := 40

def Cn : ℝ := 2

namespace MeansPack

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι)

def nrm (v : Tau → Fin P.N → ℝ) : ℝ := ∑ τ, ∑ i, |v τ i|
def U : ℝ := P.nrm P.u
def U1 : ℝ := P.nrm P.u1
def Up : ℝ := P.nrm P.up

def E0 : ℝ := (P.f : ℝ) * P.N * (P.c0 + 4 * P.N)
def L : ℝ := Real.log P.b
def LL0 : ℝ := Real.log (P.b * P.rd) * Real.log (Real.log P.x) + |P.Lp| + Real.log P.x
def indexMeanConstant : ℝ := 100 + 9 * |P.fourthRootConstant|
def CT2 : ℝ := 7 + (|P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2) / Real.log 128
def X : ℝ := P.indexMeanConstant * P.LL0 * P.Up
def H : ℝ := (⨆ τ, ⨆ i, |P.up τ i|) / (P.h0 / (4 * P.T))
def B0 : ℝ := 4 * P.f * (P.N : ℝ) ^ 2 * (1 + P.H)
def Pa : ℝ := 9 / 2 * P.f * P.N * P.m + 3 / 2 * P.f * (P.N : ℝ) ^ 2 + 6 * Cn * P.f * P.m * (P.nc + 1)
def ap (p : ℕ) : ℝ := if p ∈ P.SB then (P.cpp p + C7 * P.vdd p) * (P.Up + P.Pa) else 0
def cinf : ℝ := (1 * P.U1 + 6 * P.Pinf) / 2
def Sp : Finset ℕ := P.e.support ∪ P.SB
def cc : ℝ := ∑ p ∈ P.Sp, (P.e p + P.ap p) * Real.log p + P.cinf
def Qcc : ℝ := P.PPe + P.XW + 104 * P.L * P.Pa + 3 * P.Pinf
end MeansPack

structure Rows {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) : Prop where
  hb : 0 < P.b
  hL : 1 ≤ P.L
  hrd : 1 ≤ P.rd
  hx : 1 ≤ P.x
  hllx : 1 ≤ Real.log (Real.log P.x)
  hf : 1 ≤ P.f
  hN : 1 ≤ P.N
  hh0 : 32 * (P.f : ℝ) * (P.N : ℝ) ^ 2 ≤ P.h0
  hSZ2 : 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 ≤ P.b

namespace MeansPack

end MeansPack

end IxMeans
