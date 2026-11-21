import Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal
import Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds
import Formalism.SharpRestriction.LevelLetterCocycles.StmtLocFOfCountsAll
import Formalism.PeriodIntegrals.SqfLab
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.CardLeSumOfCover
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.CardMonicTwoRootsLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallNaturalNumbersBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.SquarefreeCountEstimate

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one

end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

end Formalism.MainNotions.N.CylinderCountFamily
