import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

abbrev LaMod (D : Datum F) (N₁ : ℕ) : Type := ZMod N₁ ⊗[ℤ] D.La

def toLaMod (D : Datum F) (N₁ : ℕ) : D.La →+ LaMod D N₁ :=
  (TensorProduct.mk ℤ (ZMod N₁) D.La 1).toAddMonoidHom

theorem toLaMod_apply (D : Datum F) (N₁ : ℕ) (a : D.La) : toLaMod D N₁ a = (1 : ZMod N₁) ⊗ₜ a := rfl

end GlobalTheory.UPel
