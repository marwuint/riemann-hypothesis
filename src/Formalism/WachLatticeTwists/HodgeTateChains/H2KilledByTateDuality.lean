import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

def cB (ℓ s m t gK : ℕ) (U : Finset ℤ) : ℕ := (Finset.range t).sup (fun e => cTB ℓ s m e gK U)

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
