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

abbrev cu_mu (X : CData) : Measure X.I.GA := X.I.muA X.μf

instance cu_sfin (X : CData) : SigmaFinite (cu_mu X) := by
  unfold cu_mu AutInst.muA
  infer_instance

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

end cu_NObj

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

end Formalism.MainNotions.LeviCoordinates
