import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_idem_spl (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

theorem rho_apply_spl (u : Pl E) (g : Gam E n u) :
    rho E n u g = (GeneralLinearGroup.map (pLoc E u) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)),
      GeneralLinearGroup.map (pLoc E (cPl E u)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := rfl

end GlobalTheory.EulerTw
