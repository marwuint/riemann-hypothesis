import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.HermitianCurvature.StatementWd
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules
import Formalism.SharpRestriction.CuspSpanNormBounds.LevelRaisingOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
import Formalism.HermitianCurvature.StatementTC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities

section PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Head

variable (k j r' : ℕ)

def slMid (p : Fin (2 * (j + r') + k + 1)) : Prop := j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j

variable {k j r'}

variable (z z' : Fin (2 * (j + r') + k + 1) → ℂ) (h : Matrix (Fin j) (Fin j) ℂ)
  (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Head

end Formalism.MainNotions.BridgeLemma₅

end PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section GlobalTheory

variable {k j r' : ℕ}

instance slMid_dec (p : Fin (2 * (j + r') + k + 1)) : Decidable (slMid k j r' p) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (o o' : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ)
  (g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end GlobalTheory

end Formalism.MainNotions.BridgeLemma₅

end PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartWdAll

noncomputable section PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdAbstract

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end WdAbstract

end Formalism.MainNotions.BridgeLemma₅

end PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartWdAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFrAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFr3

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.I

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

noncomputable def frEv (Y : ℂ) : A[X] →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A Y) (fun a => (Algebra.commutes Y a).symm)

theorem frEv_apply (Y : ℂ) (P : A[X]) : frEv Y P = P.eval₂ (RingHom.id A) (algebraMap ℂ A Y) := rfl

@[simp] theorem frEv_X (Y : ℂ) : frEv (A := A) Y X = algebraMap ℂ A Y := by simp [frEv_apply]

@[simp] theorem frEv_C (Y : ℂ) (a : A) : frEv Y (C a) = a := by simp [frEv_apply]

end Ring

end Formalism.MainNotions.BridgeLemma₅

end PartFr3

section PartFr4

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators
open scoped ContDiff

section Level

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ}

variable (C : Ctx B r) (Γ : GCtx E r)

end Level

end Formalism.MainNotions.BridgeLemma₅

end PartFr4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFr6

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators

section Res

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)

variable {C}

variable (C)

end Res

end Formalism.MainNotions.BridgeLemma₅

end PartFr6

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartFrAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartLb4

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lb_haarG : Formalism.FourierDecayAlt.B2.HaarGExists :=
  (Formalism.FourierDecayAlt.P.group_measure_from_diagonal Formalism.REAL.uJEmb Formalism.REAL.unimodular Formalism.REAL.ballFinite Formalism.REAL.volGrowth
    Formalism.QuantumDeterminants.hpkFacts Formalism.QuantumDeterminants.uHConj Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar Formalism.FourierDecayAlt.P.unitary_group_closed).1

def lbHaarUp : Prop :=
  (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ

def lbRepOfHC : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHCTypeW k r z u π →
      IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z)

end Formalism.MainNotions.BridgeLemma₅

end PartLb4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartTaAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartTa4

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartTaAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅
