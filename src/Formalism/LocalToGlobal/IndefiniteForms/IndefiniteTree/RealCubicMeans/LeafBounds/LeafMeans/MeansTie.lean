import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansPf
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

noncomputable section

open Finset

namespace IxMeans.MeansTie

def kap (N p : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) < p then (N : ℝ) - 2 * p + 1 + 2 * (i : ℕ) else -(2 * (p : ℝ)) - N + 1 + 2 * (i : ℕ)

def de (N p : ℕ) (i : Fin N) : ℝ := if (i : ℕ) < p then 0 else -1

def gap {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k + 1 < N then v ⟨k, by omega⟩ - v ⟨k + 1, h⟩ else 0

def anchored {N : ℕ} (G : ℕ → ℝ) (A : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) ≤ A then ∑ k ∈ Ico (i : ℕ) A, G k else -∑ k ∈ Ico A (i : ℕ), G k

def uMinus (N p : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := fun i => u i - c0 * de N p i

def firstVectorGaps (N p T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (k : ℕ) : ℝ :=
  ((⌊gap (fun i => uMinus N p c0 u i - kap N p i) k / ((T : ℝ) + D + 1)⌋ : ℤ) : ℝ)

def firstGapVector (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := anchored (firstVectorGaps N p T D c0 u) A

def upDef (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun i => firstGapVector N p A T D c0 u i - 3 * N * de N p i

structure Leaves (Tau : Type) where

  dE : ℕ

  level : ℕ

  q1 : ℕ

  d : ℕ

  g1 : ℕ

  g2 : ℕ

  rr : ℕ

  rr' : ℕ

  r0 : ℕ

  P0 : ℝ

  logmu : ℝ

  cubicPeriodConstant : ℝ

  c1 : ℝ

  Nc : ℕ

  bigp : Tau → ℕ

  A : ℕ

  eloc : ℕ → Finset ℝ

def cppDef (q : ℕ) : ℝ := if q = 2 then 1 else 1 / ((q : ℝ) - 1)

def XWDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) : ℝ :=
  66 * P.L + (P.nc : ℝ) * P.f * P.N * Real.log P.rd

def kpDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) (q : ℕ) : ℝ :=
  (P.nc : ℝ) * P.f * P.N * P.vdd q / 2

namespace Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (Lv : Leaves Tau) (P : MeansPack Tau ι)

def SBDef : Finset ℕ := ((range (⌊P.B0⌋₊ + 1)).filter Nat.Prime) ∪ (2 * Lv.dE * Lv.level).primeFactors

def PPeDef : ℝ :=
  3 / 2 * (P.f : ℝ) * (P.N : ℝ) ^ 4 * P.L
    + (((P.f : ℝ) * (P.N : ℝ) ^ 2 + 3) * P.f * P.N * Real.log P.rd + 3 * Real.log ((2 * Lv.q1 * Lv.d : ℕ) : ℝ))
    + (3 * Real.log ((Lv.g1 * Lv.g2 : ℕ) : ℝ) + Real.log ((Lv.rr * Lv.rr' : ℕ) : ℝ))

def Xde : ℝ := Lv.logmu + 3 * (P.D : ℝ) * P.L

def Psup : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Lv.P0 + 2 * (P.f : ℝ) * (P.N : ℝ) ^ 2

def Ptau0 : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Real.log (Real.exp (Lv.Xde P) + 1) + Lv.Psup P

def PPA : ℝ := 3 * (P.D : ℝ) + 3 * Lv.cubicPeriodConstant

def PinfDef : ℝ :=
  2 * Lv.Ptau0 P + Lv.PPA P + 2 * (P.f : ℝ) * P.N * Lv.c1 + 7 * (P.f : ℝ) * (P.N : ℝ) ^ 2 + 2 * Real.log (Lv.Nc : ℝ)

def rnd (q : ℕ) : ℝ :=
  (if q ∣ 2 * Lv.dE * Lv.level then 1 else 0) + (if q ∣ 2 * Lv.q1 * Lv.d then kpDef P q + 1 else 0)

def eDef (q : ℕ) : ℝ := (Lv.eloc q).fold max 0 (fun x => x + Lv.rnd P q)

end Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

end IxMeans.MeansTie
