import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

def aL : ∀ {p : ℕ}, (Fin (p + 1) → Co A 1) → Co A p := fun {p} =>
  Nat.rec (motive := fun p => (Fin (p + 1) → Co A 1) → Co A p) (fun _ => one0 A)
    (fun p ih β => (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (ih fun i => β i.succ)) p

theorem aL_succ {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    aL A β = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (aL A fun i => β i.succ) := rfl

theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

theorem resB_sub (h : V ≤ U) {k : ℕ} (a b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h (a - b) = resB A h a - resB A h b := rfl

theorem resB_resB {T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h' (resB A h b) = resB A h'' b := rfl

end Res

end GlobalTheory.CompanionTheory.ConeCech
