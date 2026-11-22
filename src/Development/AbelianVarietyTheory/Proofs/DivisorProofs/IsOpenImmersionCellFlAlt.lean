import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

instance isOpenImmersion_cellFl (w : ι → Equiv.Perm (Fin N)) :
    IsOpenImmersion (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) :=
  GlobalTheory.isOpenImmersion_cell _ _ _ _ _ w

end GlobalTheory.FlagZ.TautCell
