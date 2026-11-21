import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie

section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]

def IsClassMapD {LP : Type*} (dim : LP → ℕ) (rc : ∀ n, QRep g n → LP) : Prop :=
  ∀ n (π : QRep g n), IrrSm π → dim (rc n π) = n ∧ ∀ π' : QRep g n, IrrSm π' → fixK1 π'.ρ ≠ ⊥ → (rc n π = rc n π' ↔ Nonempty (π ≅ π'))

end GlobalTheory.SerSys
end
end
namespace UpperTheory.One.M

end UpperTheory.One.M
namespace DiscreteGroups.sglob.DzType.Rt
end DiscreteGroups.sglob.DzType.Rt
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
