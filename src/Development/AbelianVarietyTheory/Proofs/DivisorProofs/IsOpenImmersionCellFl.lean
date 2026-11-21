import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

instance isOpenImmersion_cellFl (w : ι → Equiv.Perm (Fin N)) :
    IsOpenImmersion (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) :=
  GlobalTheory.isOpenImmersion_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd w

end GlobalTheory.FlagZ.Univ
