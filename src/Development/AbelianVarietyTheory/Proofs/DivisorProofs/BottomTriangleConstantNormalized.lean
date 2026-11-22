import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantTripleCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleRootOfUnityTwist

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.root_unit {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1 := by
  have hQ : ζ ∈ Qbar := by
    have : IsIntegral ℚ ζ := IsIntegral.of_pow hn (h ▸ isIntegral_one)
    exact mem_algebraicClosure_iff.2 this.isAlgebraic
  refine ⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩
  have h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h3 : lamC lam ζ = lam ⟨ζ, hQ⟩ := by simp [lamC, hQ]
  have h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
  rw [h3]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4

