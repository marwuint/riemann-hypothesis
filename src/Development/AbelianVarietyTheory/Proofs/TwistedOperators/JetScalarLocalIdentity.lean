import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem om_toPair_mul : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (p : Pair T) (s x : FinPt ch.G p.small) (s' y : FinPt ch.G p.big) (v : WO (ch.G.pS p) (ch.G.pT p) → ℂ),
    ch.W.om p (ch.G.toPair p ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v =
      ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)))
        (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch p s x s' y v
  have e1 : ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) =
      (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) * ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) := by
    rw [mul_assoc]; rfl
  have e2 : ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) =
      (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)) * ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) := by
    rw [mul_assoc]; rfl
  have e3 : ∀ (a b : Formalism.L2.Theta.GA D (ch.G.V p.small)) (c d : Formalism.L2.Theta.GA D (ch.G.V p.big)),
      ch.G.toPair p (a * b) (c * d) = ch.G.toPair p a c * ch.G.toPair p b d := by
    intro a b c d
    cases p <;> simp [GlobalTheory.ChiGrid.GridData.toPair, map_mul]
  rw [e1, e2, e3, map_mul]
  rfl

end GlobalTheory.SplitMoveKappa
