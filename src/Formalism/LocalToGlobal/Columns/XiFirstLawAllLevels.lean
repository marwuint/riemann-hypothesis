import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.ChainLawPhi
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem first_sum_scalar_mul {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (psi : k → K) (vals : Finset k) (wt : K) (a : K)
    (Φ : Loc.SF k K (n' + c') (n + c)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => a * Φ x) xj = a * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj := by
  unfold Loc.E1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end Pts

end Formalism.L2.Col
