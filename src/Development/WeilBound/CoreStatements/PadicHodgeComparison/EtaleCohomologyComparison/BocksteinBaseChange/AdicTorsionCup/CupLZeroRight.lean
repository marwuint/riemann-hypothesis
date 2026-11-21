import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable (l : ℕ) [Fact l.Prime]

theorem castH_apply {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) :
    castH h1 h2 x = x.cast h1 h2 := rfl

section Cup
variable {E : Spc} {n m i j n' i' : ℤ} (hI : ZIn) (h1 : n + m = n') (h2 : i + j = i')

def cupL (x : Hl l E n i) (y : Hl l E m j) : Hl l E n' i' := ⟨_, cup_mem l hI E h1 h2 x y⟩

theorem cupL_apply (x : Hl l E n i) (y : Hl l E m j) (k : ℕ) :
    (cupL l hI h1 h2 x y).1 k = (cup (l ^ k) (x.1 k) (y.1 k)).cast h1 h2 := rfl

end Cup

end CrystallineSemistableComparison.AdicCoh
