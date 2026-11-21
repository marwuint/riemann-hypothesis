import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupFiltration
import GroundTheory.LocalFields.FormalGroups.Basics

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing GroundTheory.LocalField.FormalGroup

section FormalGroupPoints

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

namespace MaxIdealPoint

variable {F G H : FormalGroup 𝒪}

def homApply (f : Hom F G) (x : MaxIdealPoint F) : MaxIdealPoint G :=
  mk (psEvalAt (f.toPowerSeries : MvPowerSeries Unit 𝒪) fun _ => x.val)
    (psEvalAt_mem (by rw [f.constantCoeff_eq_zero']; exact zero_mem _) fun _ => x.val_mem)

theorem val_homApply (f : Hom F G) (x : MaxIdealPoint F) :
    (homApply f x).val = psEvalAt (f.toPowerSeries : MvPowerSeries Unit 𝒪) fun _ => x.val :=
  rfl

end MaxIdealPoint

end FormalGroupPoints

end

end GroundTheory.Arith.Abelian
