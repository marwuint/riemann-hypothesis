import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section defs

variable (k r : ℕ)

def Xsp : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def Wsp (z : Fin (2 * r + k + 1) → ℂ) : Set (Fin (2 * r + k + 1) → ℂ) :=
  {v | inWb k r v ∧ herm (Hpk k r) v z = 0}

def wbPart (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

def prW (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  wbPart k r v + (herm (Hpk k r) (wbPart k r v) z / (Tz k r z : ℂ)) • z

def xcof (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ b, (Zhat k r z z' g).adjugate b (Fin.last r) • (g *ᵥ fvec k r z' b)

def xcofL (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a

def omW (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ := prW k r z (xcof k r z z' g)

def omW' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)

end defs

end PI.UnitaryGroupMassFormula.GsFr
