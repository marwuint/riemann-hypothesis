import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

namespace Formalism.MainNotions.sizeConstantAtParamsWeight

open Formalism.BasicNotions NumberField Finset

structure ThFin where
  l : ℕ
  q : ℕ
  DF : ℕ
  r1 : ℕ
  phic : ℝ
  lamQ : ℝ
  nuLoc : ℝ
  minVTheta : ℝ
  vTau : ℝ

structure ThArch where
  q : ℕ
  DF : ℕ
  r1 : ℕ
  phic : ℝ
  logThetaMax : ℝ
  cuspVal : ℝ

structure JacNum where
  p : ℕ
  c : ℕ
  jac : ℝ

structure MajNum where
  lmin : ℝ
  lmax : ℝ

structure Loc (D : D7) (V : DivX D) (Lc : placeRankTwoOne.Loc D V) where

  NNH : ℕ → HLat D.what₂.LL
  inc : ∀ j, (V.MjH j).V →ₗ[D.what₂.LL] (NNH j).V
  inc_inj : ∀ j, Function.Injective (inc j)

  inc_lat : ∀ j x, x ∈ (V.MjH j).L ↔ inc j x ∈ (NNH j).L

  inc_metric : ∀ j v x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (V.MjH j).b (V.MjH j).X v x) =
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (NNH j).b (NNH j).X v (inc j x))

  goodE : ∀ j, (NNH j).V →ₗ[D.what₂.LL] (NNH j).V
  goodE_idem : ∀ j, goodE j ∘ₗ goodE j = goodE j
  goodE_range : ∀ j y, y ∈ LinearMap.range (inc j) ↔ goodE j y = y

  l1 : ∀ j c, D.what₂.Tau → ∀ w, Lc.PtF j c w → ℝ

  l2 : ∀ j c, D.what₂.Tau → ∀ w, Lc.PtF j c w → ℝ

  eV : ArithmeticCylinders.VecAt D

  ThF : Type
  thF : ThF → ThFin
  ThA : Type
  thA : ThA → ThArch

  JB : Type
  jb : JB → JacNum

  Maj : Type
  maj : Maj → MajNum

variable (D : D7) (L : SizeData₂ D) (V : DivX D) (P : DIV.Align.PrinLev V) (Lc : placeRankTwoOne.Loc D V) (B : WeightFamilies.Prov D) (X : Loc D V Lc)

structure LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) where
  fl : placeRankTwoOne.LocF Fm
  cf : WeightFamilies.ProvF Fm
  lo : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (fl x hx i)

end Formalism.MainNotions.sizeConstantAtParamsWeight

end
