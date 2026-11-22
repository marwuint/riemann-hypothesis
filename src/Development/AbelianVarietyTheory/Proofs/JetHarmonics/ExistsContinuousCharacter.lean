import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.CommutatorCharacter

variable {D : D7} {N N' : ℕ}

def vecHom (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' :=
  AddMonoidHom.mk' (vecOf D cc δ) (GlobalTheory.PlaceComponents.vecOf_add D cc δ)

end GlobalTheory.CommutatorCharacter
