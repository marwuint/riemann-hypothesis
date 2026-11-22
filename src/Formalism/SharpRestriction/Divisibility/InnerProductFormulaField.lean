import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

namespace Formalism.MainNotions.InnerProductFormulaField

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

structure Loc (D : D7) where

  Sg : Finset (Pl D)
  mem_Sg : ∀ v, v ∈ Sg ↔ ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ
  ZgSb : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ
  idxgSb : D.what₂.Tup → ℕ → Pl D → ℕ

  cCh : ℕ → ℝ
  cSb : ℕ → ℝ

  ZChR : ℕ → ℝ

  ZSbR : ℕ → ℝ

  nT : ℕ → ℝ

  massCh : ℕ → ℝ
  massSb : ℕ → ℝ
  mass_pos : ∀ j, 0 < massCh j ∧ 0 < massSb j

  LsS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  LChS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  Lfin : ℕ → ℕ → ℂ

  dFin : ℕ → ℂ

namespace Loc

end Loc

variable (D : D7) (Z : DivX D) (T : ThetaX D) (A : TH.ProvA) (X : Loc D)

section RealConstant

variable {D} {T}

structure LocC (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) where

  Vc : D.what₂.Word → Type
  [acVc : ∀ u, AddCommGroup (Vc u)]
  [moVc : ∀ u, Module ℂ (Vc u)]

  VD : D.what₂.Word → Type
  [acVD : ∀ u, AddCommGroup (VD u)]
  [moVD : ∀ u, Module ℂ (VD u)]

  ell : ∀ u, Vc u →ₗ[ℂ] VD u →ₗ[ℂ] ℂ

  vOf : ∀ u, Y.ArchDat u → Vc u

  TOf : ∀ u, Y.ArchDat u → VD u

  ellT_eq : ∀ u da, Y.ellT u da = ell u (vOf u da) (TOf u da)

  v_free : ∀ u (v : Vc u) (da : Y.ArchDat u), ∃ da', vOf u da' = v ∧ TOf u da' = TOf u da

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

end RealConstant

structure LevObj {D : D7} (T : ThetaX D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j

  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), S.Mult μ j →ₗ[ℂ] T.cusp (D.sp.Y j)

  PhiYup : ∀ (_μ : D.what₂.Tup) (j : ℕ), T.Sch (D.sp.Y j) (D.sp.Y (j + 1))

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ

structure LevDat {D : D7} (T : ThetaX D) where
  EE : Type
  [nacg : NormedAddCommGroup EE]
  [ips : InnerProductSpace ℂ EE]
  [fd : FiniteDimensional ℂ EE]
  S : RowSide D EE
  n : ℕ
  b : OrthonormalBasis (Fin n) ℂ EE
  ty : Fin n → D.what₂.FT
  V : LevObj T S

attribute [instance] LevDat.nacg LevDat.ips LevDat.fd

end Formalism.MainNotions.InnerProductFormulaField

end
