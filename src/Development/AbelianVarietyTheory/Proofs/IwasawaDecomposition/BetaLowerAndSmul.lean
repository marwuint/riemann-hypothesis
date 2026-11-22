import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
