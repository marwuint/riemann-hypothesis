import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

end act

end GlobalTheory.UPel.HT.EtLev
