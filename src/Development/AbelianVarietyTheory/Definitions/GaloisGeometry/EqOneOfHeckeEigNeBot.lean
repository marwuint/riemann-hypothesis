import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh

variable {G : GDatum} {gb : GBase G ℂ}

abbrev Z {N : ℕ} (X : GenModel gb N) (k : ℕ) : Scheme.{0} := (GlobalTheory.KS.pow X.univ.A k).left

def zs {N : ℕ} (X : GenModel gb N) (k : ℕ) : Z X k ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def corrOp {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (c1 c2 : Y ⟶ Z) [IsFinite c1] [Etale c1]
    (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (a b : ℕ) : hodgeH s a b →ₗ[ℂ] hodgeH s a b :=
  hodgeTrace h1 a b ∘ₗ hodgePull h2 a b

end GlobalTheory.W2
