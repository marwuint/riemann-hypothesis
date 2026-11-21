import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.MeansTie
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansBridge
import Development.WeilBound.SupplementaryPages.FaceFrameMatrix

noncomputable section

open Finset NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.IndefR.Obj

namespace IxMeans.MeansTie2

open IxMeans IxMeans.MeansTie

def nX (f r jp : ℕ) : ℕ := f * jp * (r - jp)

def zeroConstantLowerBound (f r jp : ℕ) : ℕ := max (r + (nX f r jp + 1).choose 2 + 2) (8 * f * r + 4)

def leastMultipleEightBound (f r jp : ℕ) : ℕ := 8 * ((zeroConstantLowerBound f r jp + 7) / 8)

structure PgNums where

  Nr : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  jp : ℕ

  DY : ℝ

  T : ℝ

  b : ℝ

  x : ℝ

  rd : ℝ

  Lc : ℝ

  eta : ℝ

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def pgOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) : PgNums where
  Nr := (faceLiftPage R F I J hd).Nr
  f := (faceLiftPage R F I J hd).f
  m := (faceLiftPage R F I J hd).m
  k := (faceLiftPage R F I J hd).k
  jp := (faceLiftFactor R F I J hd j).q'
  DY := (faceLiftFactor R F I J hd j).DY
  T := (faceLiftFactor R F I J hd j).T
  b := (faceLiftPage R F I J hd).b
  x := (faceLiftPage R F I J hd).x
  rd := (faceLiftPage R F I J hd).rd
  Lc := (faceLiftPage R F I J hd).Lc
  eta := (faceLiftPage R F I J hd).η

variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

structure PackPage (r4 : ℝ) (P : MeansPack Tau ι) (pg : PgNums) : Prop where
  hN : (P.N : ℝ) = pg.Nr
  hf : (P.f : ℝ) = pg.f
  hm : (P.m : ℝ) = pg.m
  hjp : P.jp = pg.jp
  hD : (P.D : ℝ) = pg.DY
  hT : (P.T : ℝ) = pg.T
  hb : P.b = pg.b
  hx : P.x = pg.x
  hrd : P.rd = pg.rd
  hLp : P.Lp = pg.Lc

  hh0 : P.h0 = pg.eta / pg.m

  hc0 : P.c0 = (leastMultipleEightBound P.f P.N P.jp : ℝ)

  hnc8 : 8 ∣ P.nc
  hnc1 : 8 * P.f * P.N + 4 ≤ P.nc
  hnc2 : P.nc ≤ 16 * P.f * P.N ^ 2 + 8

  fourth_root_eq : P.fourthRootConstant = r4

end IxMeans.MeansTie2
