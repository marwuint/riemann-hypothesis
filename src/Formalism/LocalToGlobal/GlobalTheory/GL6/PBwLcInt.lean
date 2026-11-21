import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem bwL_descent (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E)
    (he : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.inclE (F := F) (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AF F) e ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.SS F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨D, hD, hDe⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  set d : E := algebraMap F E (D : F) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; intro h
    exact hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))
  have hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range := by
    intro k
    have := hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)
    rwa [Algebra.smul_def] at this
  let f : 𝓞 E →ₗ[ℤ] E := LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
  have hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    obtain ⟨y, hy⟩ := hpow k
    exact ⟨y, by simp [f, hy, hd0]⟩
  have : IsNoetherian ℤ (LinearMap.range f) := by
    exact isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have : IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule := isNoetherian_of_le hS
  have hint : IsIntegral ℤ e :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e
      (Algebra.subset_adjoin (Set.mem_singleton e))
  exact ⟨⟨e, hint⟩, rfl⟩

variable (D : D7) (u : D.what₂.Word)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
