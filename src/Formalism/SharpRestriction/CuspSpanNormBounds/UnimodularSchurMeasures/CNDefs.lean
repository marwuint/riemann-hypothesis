import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Mathlib
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

structure CSize (X : CData) where
  tau1 : X.I.GA → ℝ
  I0 : Set X.I.GA
  str : ∀ J : ℕ, Composition J → Set X.I.GA
  tau : ∀ (J : ℕ) (c : Composition J), X.I.GA → Fin c.length → ℝ
  kap : ∀ J : ℕ, Composition J → ℝ

def CSize.Strata {X : CData} (S : CSize X) : Prop :=
  Measurable S.tau1 ∧ (∀ J c, MeasurableSet (S.str J c)) ∧ (∀ J c, Measurable (S.tau J c)) ∧
    (∀ x, x ∈ S.I0 ∨ ∃ J, 1 ≤ J ∧ J ≤ X.qq ∧ ∃ c, x ∈ S.str J c) ∧ (∀ x ∈ S.I0, S.tau1 x = 1 / 2) ∧
    (∀ x, 0 < S.tau1 x ∧ S.tau1 x ≤ 1 / 2) ∧
    ∀ J c, ∀ x ∈ S.str J c, ∀ a, S.tau1 x ≤ S.tau J c x a

end Formalism.MainNotions.LeviCoordinates

end
