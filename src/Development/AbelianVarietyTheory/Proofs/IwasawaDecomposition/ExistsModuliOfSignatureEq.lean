import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.ModuliGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_eq_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) :
    ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

end GlobalTheory.ModuliGenus
