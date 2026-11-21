import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantAlgebraComparison.InvAlgOfSteps

noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem hmat_mul (I : AutInst) (g h : HAd I) : hmat I (g * h) = hmat I g * hmat I h := rfl

theorem hmat_one (I : AutInst) : hmat I 1 = 1 := rfl

end PI.UnitaryGroupMassFormula.BridgeInvAlg
