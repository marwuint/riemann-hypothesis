import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Mathlib
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.LatticeRigidity.StatementD

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cu_mu (X : CData) : Measure X.I.GA := X.I.muA X.μf

instance cu_sfin (X : CData) : SigmaFinite (cu_mu X) := by
  unfold cu_mu AutInst.muA
  infer_instance

def cu_cst (X : CData) (ν : Measure X.I.GA) (f : X.I.GA → ℂ) (x : X.I.GA) : ℂ := ∫ m, f (m * x) ∂ν

structure cu_NObj (X : CData) where
  μN : ∀ v : InfinitePlace X.I.F, Measure (Formalism.REAL.UJ (X.I.ε v))
  [sN : ∀ v, SigmaFinite (μN v)]
  μNf : Measure X.I.Gf
  [sNf : SigmaFinite μNf]
  lam : Measure X.I.GA

attribute [instance] cu_NObj.sN cu_NObj.sNf

namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def μNA : Measure X.I.GA := (Measure.pi O.μN).prod O.μNf

def IsOn (W : Submodule X.I.E (Fin X.I.n → X.I.E)) : Prop := O.μNA (X.I.NA W)ᶜ = 0

def IsWeil : Prop :=
  ∀ F : X.I.GA → ℂ, Integrable F (cu_mu X) → ∫ y, F y ∂(cu_mu X) = ∫ y, ∫ n, F (n * y) ∂O.μNA ∂O.lam

def CstInv (ν : Measure X.I.GA) (f : X.I.GA → ℂ) : Prop :=
  ∀ᵐ y ∂O.lam, ∃ c : ℂ, ∀ᵐ n ∂O.μNA, cu_cst X ν f (n * y) = c

end cu_NObj

namespace cu

end cu

namespace cu

end cu

namespace cu

end cu

namespace cu

end cu

namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def IsWeilNull : Prop :=
  ∀ Z : Set X.I.GA, cu_mu X Z = 0 → ∀ᵐ y ∂O.lam, ∀ᵐ n ∂O.μNA, n * y ∉ Z

def RInv (v : InfinitePlace X.I.F) : Prop :=
  ∀ᵐ n₀ ∂(O.μN v), ∀ F : Formalism.REAL.UJ (X.I.ε v) → ℂ, ∫ n, F (n * n₀) ∂(O.μN v) = ∫ n, F n ∂(O.μN v)

def LocZero (v : InfinitePlace X.I.F) : Prop :=
  ∀ a : Formalism.REAL.UJ (X.I.ε v), ∀ᵐ b ∂(Formalism.REAL.muG (X.I.ε v)),
    ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) (a⁻¹ * (n * b)) ∂(O.μN v) = 0

end cu_NObj

namespace cu

variable (X : CData)

def UnipFine : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∃ O : cu_NObj X, O.IsOn W ∧ O.IsWeil ∧ O.IsWeilNull ∧
    O.μNA ≠ 0 ∧ ∃ v, O.RInv v ∧ O.LocZero v

end cu

namespace cu

end cu

end Formalism.MainNotions.LeviCoordinates
