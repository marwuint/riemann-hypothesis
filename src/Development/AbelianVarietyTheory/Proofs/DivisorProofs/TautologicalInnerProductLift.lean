import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self toMod coord ofSec mkSec sec_ext)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB GlobalTheory.ProjSpace GlobalTheory.QCoh
open GlobalTheory.CxPts GlobalTheory.HermFrame
open scoped ZeroObject ComplexOrder

namespace GlobalTheory.TautFlag

abbrev Q : (PSpace ℤ 1).Modules := toMod (O1 ℤ 1)

abbrev E : (PSpace ℤ 1).Modules := freeModule (PSpace ℤ 1) (Fin 2)

def X' (j : Fin 2) : Γ(Q, ⊤) := ofSec (ProjSpace.coord ℤ 1 j) ⊤

def sec : Fin 2 → Γ(Q, ⊤) := ![-X' 1, X' 0]

def quotMap : E ⟶ Q := sectionsHom sec

theorem resM_X' (j : Fin 2) : resM Q (le_top : chart ℤ 1 j ≤ ⊤) (X' j) = LB.chartSec (O1_isLB ℤ 1) j :=
  sec_ext fun i => by
    rfl

theorem chartSec_mem_span (j : Fin 2) : resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) ∈
    Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 j)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 j ≤ ⊤) (sec i)) := by
  have e : resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) =
      resM Q (le_top : chart ℤ 1 j ≤ ⊤) (X' j) := (resM_self _ _).trans (resM_X' j).symm
  rw [e]
  fin_cases j
  · exact Submodule.subset_span ⟨1, rfl⟩
  · have h : resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec 0) ∈ Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 1)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec i)) := Submodule.subset_span ⟨0, rfl⟩
    have e : resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (X' 1) = -resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec 0) := by
      rw [← map_neg]
      exact congrArg _ (neg_neg _).symm
    change resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (X' 1) ∈ Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 1)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec i))
    rw [e]
    exact Submodule.neg_mem _ h

instance epi_quotMap : Epi quotMap := by
  have := LB.isQuasicoherent_toMod (O1_isLB ℤ 1)
  refine (epi_sectionsHom_iff sec).2 (spanStalks_of_forall_exists_affine sec fun x => ?_)
  obtain ⟨j, hj⟩ := exists_mem_chart ℤ 1 x
  refine ⟨_, isAffineOpen_chart ℤ 1 j, hj, top_le_iff.1 fun q _ => ?_⟩
  have e := (LB.chartEquiv (O1_isLB ℤ 1) j (le_refl (chart ℤ 1 j))).symm_apply_apply q
  have e₂ : q = _ • resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) :=
    e.symm.trans (LB.chartEquiv_symm_apply (O1_isLB ℤ 1) j (le_refl (chart ℤ 1 j)) _)
  refine e₂ ▸ Submodule.smul_mem _ _ ?_
  exact chartSec_mem_span j

variable {σ : ℤ →+* ℂ}

end GlobalTheory.TautFlag
