import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CanExtM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {V : X.Opens}

section API

variable {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : GlobalTheory.LogDR.Chart t V)

def rangeSub : Submodule Γ(X, c.U.1) c.S where
  carrier := Set.range (algebraMap Γ(X, c.U.1) c.S)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ a b⟩
  smul_mem' := by rintro r _ ⟨a, rfl⟩; exact ⟨r * a, by rw [map_mul, Algebra.smul_def]⟩

end API

end GlobalTheory.CanExtM
