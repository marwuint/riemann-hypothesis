import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LDblPf

instance monoSch {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map U.ι).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

instance freePres (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1} R)) := (ModuleCat.adj _).leftAdjoint_preservesColimits
  unfold free freeP
  infer_instance

end LateralTheory.EtaleTrace.LDblPf
