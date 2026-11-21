import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

noncomputable section

namespace Formalism.MainNotions.IntegralModelsLocalData

open Formalism.BasicNotions Formalism.MainNotions.ModuliIntegralCharts

structure Comparison₂ (D : D7) (P : ModuliIntegralCharts.Prov D) (w : P.Dat) (Sh : DV.ShimX D.what₂.Tau) where
  rk_eq : P.rk w = Sh.N
  jj_eq : P.jj w = Sh.j

  fcOf : ∀ p : ℕ, p.Prime → (P.loc w p).Gen (P.loc w p).Xm → Sh.FibComp p
  fcOf_surj : ∀ (p : ℕ) (hp : p.Prime), Function.Surjective (fcOf p hp)
  fibInBd_iff : ∀ (p : ℕ) (hp : p.Prime) η, (Sh.fibInBd p (fcOf p hp η) ↔ ¬ (P.loc w p).abAt η)

  curveHT : ∀ (p : ℕ) n Z', p.Prime → 3 ≤ n →
    (P.loc w p).IsHTBlowup Z' ((P.loc w p).Xn n) → ∀ c : Sh.CurveHT p,
      ∃ (C : (P.ex w p).CrvS Z') (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Sh.N),
        (m : ℝ) * Sh.degHT p c (τ, i) = (P.ex w p).degGr C (D.eTau τ) (i + 1)

  curveDR : ∀ p : ℕ, p.Prime → p ≠ 2 → DV.UnramE D p → p ∉ Sh.lev → ∀ c : Sh.CurveDR p,
      ∃ (CC : (P.loc w p).Crv) (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Sh.N),
        (m : ℝ) * Sh.degDR p c (τ, i) = (P.ex w p).degGrD CC (D.eTau τ) (i + 1)

structure Prov (D : D7) (XD : DivX D) where

  P : ModuliIntegralCharts.Prov D

  dat_surj : letI := D.host.cmStar; ∀ S κ, DV.HidaSetting D XD S κ → ∃ w, Nonempty (Comparison₂ D P w (XD.shv S κ))

variable (D : D7) (XD : DivX D) (X : Prov D XD)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

abbrev ProvF : Type 1 := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Prov (Fm.D x i) (Fm.X x i)

variable (XF : ProvF Fm)

end Family

end Formalism.MainNotions.IntegralModelsLocalData

end
