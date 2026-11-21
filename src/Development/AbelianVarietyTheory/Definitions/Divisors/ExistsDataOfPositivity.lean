import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

def mulG (j : ℕ) : (Fin G.N → F) →ₗ[F] G.global j →ₗ[F] G.global (j + 1) :=
  LinearMap.mk₂ F (fun u f => ⟨G.mulW j u f, mulW_mem_global G j u f.2⟩)
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))

def lat (j : ℕ) : Submodule (𝓞 F) (G.global j) :=
  Nat.rec (motive := fun j => Submodule (𝓞 F) (G.global j))
    (Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global 0))))
    (fun j M => Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global (j + 1)))) ⊔
      Submodule.map₂ ((mulG G j).restrictScalars₁₂ (𝓞 F) (𝓞 F)) G.lattice M) j

theorem basis_mem_lat (j : ℕ) (i) : Module.finBasis F (G.global j) i ∈ lat G j := by
  cases j with
  | zero => exact Submodule.subset_span ⟨i, rfl⟩
  | succ j => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem isFull_lat (j : ℕ) : IsFull (lat G j) := by
  refine ⟨?_, top_le_iff.1 ((Module.finBasis F (G.global j)).span_eq.ge.trans
    (Submodule.span_mono (Set.range_subset_iff.2 (basis_mem_lat G j))))⟩
  induction j with
  | zero => exact Submodule.fg_span (Set.finite_range _)
  | succ j ih =>
    have h : G.lattice.FG := Submodule.fg_span (Set.finite_range _)
    exact (Submodule.fg_span (Set.finite_range _)).sup (h.map₂ _ ih)

def data (T : ℕ) (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β) : Data F :=
  { G.globalData T hT with M := lat G, full := isFull_lat G, beta := β, one_le_beta := hβ, J := J }

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)

end GlobalTheory.HilbertSamuel.Model
