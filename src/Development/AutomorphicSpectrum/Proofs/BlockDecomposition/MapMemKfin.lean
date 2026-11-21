import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

def expG (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp ((t : ℂ) • X)).unit

@[simp] theorem coe_expG (X : Mat n) (t : ℝ) : ((expG X t : G n) : Mat n) = NormedSpace.exp ((t : ℂ) • X) := rfl

def e1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def f1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) + Complex.I • D (Matrix.single a b Complex.I))

def e2 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -f1 D b a

end GlobalTheory.CompanionTheory.GLK

end
