import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.Sandwich

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)

theorem restr_mulPole (j : ℕ) (f : H0 R.str (R.adj j) ⊤) :
    H0.restr le_top (R.mulPole j ⊤ f) = R.mulPole j R.off (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulPole_injective (h₁ : FreeOnOpen TF.X Z U P.u₁) (j : ℕ) : Function.Injective (R.mulPole j R.off) :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).injective

theorem nowhereZero_pow_zero : NowhereZero (H0.ofSec R.str ⊤ (R.Δ₁.pow 0)) := nowhereZero_of_exists fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart R.Δ₁.isLB y
  exact ⟨fun _ => i, mem_zpow_U.2 hi, by rw [R.Δ₁.germ_pow R.str 0 i y hy hi, pow_zero]; exact isUnit_one⟩

end GlobalTheory.HSApp.Sandwich

