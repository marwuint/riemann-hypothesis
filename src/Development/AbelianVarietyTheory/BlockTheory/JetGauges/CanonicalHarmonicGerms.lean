import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def column {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

@[simp] theorem column_apply {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) (ℓ : Lt1 Dw) :
    column m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms
