import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.FibTriv

def prodPt {d : ℕ} (z : V d) (x : ℂ) : V (d + 1) := WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) z.ofLp x)

def basePt {d : ℕ} (v : V (d + 1)) : V d := WithLp.toLp 2 fun a => v a.castSucc

@[simp] theorem prodPt_castSucc {d : ℕ} (z : V d) (x : ℂ) (a : Fin d) : prodPt z x a.castSucc = z a := by
  simp [prodPt]

@[simp] theorem prodPt_last {d : ℕ} (z : V d) (x : ℂ) : prodPt z x (Fin.last d) = x := by simp [prodPt]

@[simp] theorem basePt_apply {d : ℕ} (v : V (d + 1)) (a : Fin d) : basePt v a = v a.castSucc := rfl

@[simp] theorem basePt_prodPt {d : ℕ} (z : V d) (x : ℂ) : basePt (prodPt z x) = z := by
  ext a; simp

@[simp] theorem prodPt_basePt {d : ℕ} (v : V (d + 1)) : prodPt (basePt v) (v (Fin.last d)) = v := by
  ext a
  induction a using Fin.lastCases <;> simp

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}
  (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (hE : IsVB E 2) (cE : Chart E 2)
  (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)

end GlobalTheory.FibTriv
