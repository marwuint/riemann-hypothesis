import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_rfl {n i : ℤ} (x : Ht q E n i) : x.cast rfl rfl = x := rfl

theorem cast_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_add {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    (x + y).cast h1 h2 = x.cast h1 h2 + y.cast h1 h2 := by
  subst h1 h2; rfl

def castH {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast h1 h2
  map_zero' := cast_zero h1 h2
  map_add' := cast_add h1 h2

theorem red_cast (Q q' : ℕ) {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht Q E n i) :
    red Q q' E n' i' (x.cast h1 h2) = (red Q q' E n i x).cast h1 h2 := by
  subst h1 h2; rfl

end Cast

variable (l : ℕ) [Fact l.Prime]

theorem neZero_pow (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem mem_hl {E : Spc} {n i : ℤ} (x : ∀ k, HtL l k E n i) :
    x ∈ HlSub l E n i ↔ ∀ k, red (l ^ (k + 1)) (l ^ k) E n i (x (k + 1)) = x k := Iff.rfl

theorem cup_mem (hI : ZIn) (E : Spc) {n m i j n' i' : ℤ} (h1 : n + m = n') (h2 : i + j = i') (x : Hl l E n i) (y : Hl l E m j) :
    (fun k => ((cup (l ^ k) (x.1 k) (y.1 k)).cast h1 h2 : HtL l k E n' i')) ∈ HlSub l E n' i' := by
  intro k
  have := neZero_pow l (k + 1)
  have h := (hI.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) E).1 (x.1 (k + 1)) (y.1 (k + 1))
  change red _ _ _ _ _ ((cup _ _ _).cast _ _) = (cup _ _ _).cast _ _
  rw [red_cast, h, x.2 k, y.2 k]

variable {l} {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l)

end CrystallineSemistableComparison.AdicCoh
