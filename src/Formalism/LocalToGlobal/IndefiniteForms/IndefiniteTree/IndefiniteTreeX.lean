import Mathlib
import Formalism.LatticeSlopes.Statement
import Formalism.HarderNarasimhan.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.MulXProjQExact
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.BasisZeroEqSingle
import Formalism.PeriodIntegrals.EagonNorthcott

noncomputable section

open Complex

universe u

namespace Formalism.L2.Indef.Tree

def completedOddL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  (((d : ℝ) / Real.pi : ℝ) : ℂ) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * DirichletCharacter.LFunction χ s

def reducedForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc 1 |D| ×ˢ (Finset.Icc (-|D|) |D| ×ˢ Finset.Icc 1 |D|))).filter fun f =>
    f.2.1 ^ 2 - 4 * f.1 * f.2.2 = D ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧
      ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1) ∧ Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1

def formRoot (D : ℤ) (f : ℤ × ℤ × ℤ) : ℂ :=
  (-(f.2.1 : ℂ) + Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) / (2 * (f.1 : ℂ))

namespace KoszulExact

end KoszulExact

namespace EagonNorthcott

end EagonNorthcott

open scoped InnerProductSpace

end Formalism.L2.Indef.Tree
