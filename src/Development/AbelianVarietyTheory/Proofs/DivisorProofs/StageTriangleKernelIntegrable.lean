import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageConv

theorem m_le_of_size {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : D.R.m ≤ D.R.r + 1 := by
  have h4 : D.R.m ^ 4 ≤ D.R.f := h.2.2.1
  have hm : 44 ≤ D.R.m := h.2.2.2.1
  have hfm : D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 := h.2.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have h1 : (D.R.r + 1) ^ 3 < D.R.m ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : D.R.m ^ 3 ≤ D.R.m ^ 4 * D.R.m := by
    calc D.R.m ^ 3 ≤ D.R.m ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = D.R.m ^ 4 * D.R.m := by ring
  have h3 : D.R.m ^ 4 * D.R.m ≤ D.R.f * D.R.m := Nat.mul_le_mul_right _ h4
  omega

theorem rank_lt {D : D7} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} (hmr : D.R.m ≤ D.R.r + 1)
    (hp : p ≤ pp D j) (hq : q ≤ qq D j) (hA : A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p)
    (hA' : A'.rank + 2 * qq D j = rankV D i j + 2 * q) (hd : A.rank + A'.rank = WW.rank) :
    WW.rank < 2 * (A.rank - p) := by
  have e1 : rankV D ((i : ℕ) + 1) ((j : ℕ) + 1) = rankV D i j + D.R.t + sLen D := by
    simp only [rankV]; ring
  have hpp : 2 * pp D j ≤ D.R.m - 1 := by
    simp only [pp]; have := j.2; omega
  have hs : sLen D = D.R.r + 6 := rfl
  rw [e1] at hA
  omega

end GlobalTheory.StageConv
