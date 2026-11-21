import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.Normal

variable {K : Type} [Field K]

def pr {n : ℕ} (d : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun v := ∑ r, d r * v r
  map_add' v v' := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring

theorem pr_apply {n : ℕ} (d v : Fin n → K) : pr d v = ∑ r, d r * v r := rfl

variable {m n : ℕ} {D c : Fin m → Fin n → K}

end GlobalTheory.GrCl.Normal
