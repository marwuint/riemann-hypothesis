import Mathlib
import Formalism.PeriodIntegrals.UnitaryDense

open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UnitaryDenseWork

end PI.UnitaryDenseWork

open PI.UnitaryDenseWork

theorem unitaryDense_of (h : PI.FramesDense) : PI.UnitaryDense := by
  intro n P hP
  let e : Unit × Fin n × Fin n ≃ Fin n × Fin n := Equiv.punitProd _
  have hR : rename e.symm P = 0 := by
    refine h Unit n (fun _ => 1) (fun _ => Matrix.PosDef.one) (rename e.symm P) ?_
    intro y hy
    rw [eval_rename]
    have h1 := hP (y ()) (by simpa using hy ())
    exact h1
  exact rename_injective _ e.symm.injective (by rw [hR, map_zero])
