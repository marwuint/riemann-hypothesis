import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TruncQuotSymmTruncTensor
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

namespace GlobalTheory.UPel.HT.WPart

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.IwLevel GlobalTheory.DrinLev.HT IsLocalRing

variable {p : ℕ} [Fact p.Prime]

instance neZero_m (D : Datum p) : NeZero D.m := ⟨D.m_pos.ne'⟩

structure WProj (D : Datum p) {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] (b : Base D Ow) (i₀ : Fin D.a) where

  π : ℤ_[p] ⊗[ℤ] D.O →+* Matrix (Fin D.m) (Fin D.m) Ow

  surj : Function.Surjective π

  padic : ∀ c : ℤ_[p], π (c ⊗ₜ 1) = Matrix.scalar (Fin D.m) (algebraMap ℤ_[p] Ow c)

  scalar : ∀ c : 𝓞 D.F, π (1 ⊗ₜ algebraMap (𝓞 D.F) D.O c) = Matrix.scalar (Fin D.m) (b.t i₀ c)

variable {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow} {i₀ : Fin D.a}

namespace WPartOf

end WPartOf

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

end GlobalTheory.UPel.HT.WPart
