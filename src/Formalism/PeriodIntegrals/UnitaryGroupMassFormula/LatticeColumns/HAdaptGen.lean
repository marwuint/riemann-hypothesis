import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdapt

noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {K : Type} [Field K] (O : Subring K) {r k : ℕ}

def colv (c : Idx r k → Idx r k → K) (y : Fin k → Idx r k → K) : Idx r k → Idx r k → K
  | Sum.inr (Sum.inl (Sum.inl i)) => y i
  | Sum.inl a => c (Sum.inl a)
  | Sum.inr (Sum.inl (Sum.inr u)) => c (Sum.inr (Sum.inl (Sum.inr u)))
  | Sum.inr (Sum.inr b) => c (Sum.inr (Sum.inr b))

def ofCols (v : Idx r k → Idx r k → K) : Matrix (Idx r k) (Idx r k) K := fun i j => v j i

section Gen

def IntO (M : Matrix (Idx r k) (Idx r k) K) : Prop := ∀ i j, M i j ∈ O

end Gen

end PIW.MassDataColumns
