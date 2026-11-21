import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def homRe {E : Type} [Field E] {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (x : HomE E a b) : HomE E a' b' :=
  (LinearEquiv.funCongrLeft E E (finCongr hb.symm)).toLinearMap ∘ₗ x ∘ₗ
    (LinearEquiv.funCongrLeft E E (finCongr ha.symm)).symm.toLinearMap

theorem intOff_zero (S : Finset ℕ) : IntOff S 0 := by
  refine ⟨zero_mem _, fun p _ lam _ => ?_⟩
  unfold TaylorLogMetric.lamC
  split_ifs with h
  · have e : (⟨0, h⟩ : TaylorLogMetric.Qbar) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  · rw [norm_zero]
    exact zero_le_one

end Formalism.L2.PairingIndexBounds.F
