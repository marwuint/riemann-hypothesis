import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
import GroundTheory.AutomorphicForms.AnisotropicDivisionCompact
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Unitary

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

theorem lid_hermValue (ξ : ι → K ⊗[K] E) :
    Algebra.TensorProduct.lid K E (hermValue K H K ξ) =
      (fun i => conj K E (Algebra.TensorProduct.lid K E (ξ i))) ⬝ᵥ
        (H *ᵥ fun i => Algebra.TensorProduct.lid K E (ξ i)) := by
  unfold hermValue
  change ((Algebra.TensorProduct.lid K E : K ⊗[K] E ≃ₐ[K] E) : K ⊗[K] E →+* E) (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  congr 1
  · funext i
    simp only [Function.comp_apply, RingHom.coe_coe]
    exact lid_conjBase (ξ i)
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a c
    simp [baseMatrix]

theorem anisotropic_tensor (haniso : ∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0) :
    ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0 := by
  intro ξ hξ
  have h1 := haniso (fun i => Algebra.TensorProduct.lid K E (ξ i))
    (by rw [← lid_hermValue, hξ, map_zero])
  funext i
  exact (Algebra.TensorProduct.lid K E).injective (by simpa using congrFun h1 i)

variable [NumberField K]

theorem compactSpace_unitaryQuotient_of_anisotropic (hH : IsUnit H.det)
    (haniso : ∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0) :
    CompactSpace (RightCosetSpace (unitaryDiagonal K H).range) :=
  compactSpace_unitaryQuotient_of_anisotropic' H hH (anisotropic_tensor H haniso)

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

end Unitary

end Anisotropic

end

end GroundTheory.Automorphic
