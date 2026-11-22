import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions.PDVS

open Formalism.BasicNotions MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def car {D : D7} (X : ThetaX D) (μ : ℕ → X.Chr) (s i : ℕ) : X.Chr :=
  if Even i then μ s * X.etaT⁻¹ else μ s

def bB {D : D7} (X : ThetaX D) (t j : ℕ) (pos : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (φ : X.AF (X.Xs t j)) (F : X.cusp (X.Ys t j)) : ℂ :=
  X.Bj t j pos s (X.conjAF _ φ) F

section Instance

variable {D : D7}

def muOf (T : ThetaX D) (μ : D.what₂.Tup) : ℕ → T.Chr := fun s => T.chrOf μ s

end Instance

structure Loc2 (D : D7) (X : ThetaX D) where
  GA : TH.HSp D → Type
  [gaGrp : ∀ V, Group (GA V)]
  actA : ∀ V, GA V →* Module.End ℂ (X.AF V)
  actA_cusp : ∀ V g, ∀ F ∈ X.cusp V, actA V g F ∈ X.cusp V
  om : ∀ W V, X.Chr → X.Chr → GA W →* Module.End ℂ (X.Sch W V)
  posDn : ∀ t j, Odd t → D.R.r + 5 ≤ t → j + 1 < D.R.m → X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) →
    X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)
  Q : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → Type
  [msQ : ∀ t j p, MeasurableSpace (Q t j p)]
  nu : ∀ t j p, Measure (Q t j p)
  rep : ∀ t j p, Q t j p → GA (X.Ys t (j + 1))
  SchP : ℕ → ℕ → Type
  tens : ∀ t j, X.Sch (X.Xs t j) (X.Xs t (j + 1)) →
    X.FJd (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → SchP t j
  perP : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → X.Chr → SchP t j →
    X.cusp (X.Xs t j) → X.cusp (X.Ys t (j + 1)) → ℂ
  perP_tens : ∀ t j p χ Φ' s' φ F,
    perP t j p χ (tens t j Φ' s') φ F = bB X t (j + 1) p s' (X.th _ _ χ χ Φ' φ) F
  flat : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) →
    X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j) → X.Sch (X.Ys t (j + 1)) (X.Ys t j) → SchP t j
  see : ∀ t j, X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j) → X.Sch (X.Ys t (j + 1)) (X.Ys t j) →
    X.Sch (X.Xs t j) (X.Xs t (j + 1))

attribute [instance] Loc2.gaGrp Loc2.msQ

end Formalism.MainNotions.PDVS

end
