import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sig_apply (D : D7) (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hE_repr (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (W.frame.repr x) (W.frame.repr y) = W.hT x y := by
  conv_rhs => rw [← W.frame.sum_repr x, ← W.frame.sum_repr y]
  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
    map_smul, smul_eq_mul, sig_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
