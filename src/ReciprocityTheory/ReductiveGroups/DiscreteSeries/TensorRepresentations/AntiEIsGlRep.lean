import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)

end ReciprocityTheory.ChartRestriction.DS
