import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongOpen

variable (L : Type) [Field L] [NumberField L]

local notation "A" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {L} {d : ℕ} (b : Module.Basis (Fin d) ℤ (𝓞 L))

def coordSub : AddSubgroup (AfE ℚ L) where
  carrier := {t | ∃ z : Fin d → A, (∀ i, z i ∈ intAd ℚ) ∧ ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i = t}
  zero_mem' := ⟨0, fun _ => zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', fun i => add_mem (hz i) (hz' i), by
      simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, fun i => neg_mem (hz i), by simp [TensorProduct.tmul_neg]⟩

end GlobalTheory.CongOpen

namespace GlobalTheory.CongOpen

end GlobalTheory.CongOpen
