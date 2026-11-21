import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.BasicNotions.Examples₂ NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Tow (D : D7) (t : ℕ) where
  Xs : ℕ → HSp D
  Xs_rank : ∀ j, j ≤ D.R.m → (Xs j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ j, j ≤ D.R.m → (Xs j).SigOK ∧ (Xs j).IsDefinite
  Ys : ℕ → HSp D
  Ys_rank : ∀ j, j ≤ D.R.m → (Ys j).rank = D.R.r + j * t
  Ys_sig : ∀ j, j ≤ D.R.m → (Ys j).SigOK
  iXYs : ∀ j, (Xs j).V →ₗ[D.host.E] (Ys j).V
  iXYs_isom : ∀ j, j < D.R.m → HSpace.IsIsomEmb (Xs j) (Ys j) (iXYs j)
  iYXm : (Ys D.R.m).V →ₗ[D.host.E] (Xs D.R.m).V
  iYXm_isom : HSpace.IsIsomEmb (Ys D.R.m) (Xs D.R.m) iYXm

def recTow (D : D7) : Tow D D.R.t where
  Xs := D.sp.X
  Xs_rank := fun j hj => D.sp.X_rank j hj
  Xs_sig := fun j hj => ⟨D.sp.X_sig j, D.sp.X_def j hj⟩
  Ys := D.sp.Y
  Ys_rank := fun j hj => D.sp.Y_rank j hj
  Ys_sig := fun j _ => D.sp.Y_sig j
  iXYs := D.sp.iXY
  iXYs_isom := D.sp.iXY_isom
  iYXm := D.sp.iX'.comp D.sp.eYm.symm.toLinearMap
  iYXm_isom := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm

end Formalism.MainNotions.Inhab

end
