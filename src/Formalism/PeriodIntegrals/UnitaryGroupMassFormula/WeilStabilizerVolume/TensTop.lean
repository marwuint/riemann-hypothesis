import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance secondCountable_tens [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

instance borelSpace_tens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

instance borelSpace_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR R σ n) := ⟨rfl⟩

variable [LocallyCompactSpace R] [T2Space R]

theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  haveI : T2Space (R ⊗[F] E) := T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  show IsClosed {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | ∀ a b, sigR R σ (S b a) = S a b}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun c => isClosed_eq
    (hsig.comp ((continuous_apply a).comp (continuous_apply c)))
    ((continuous_apply c).comp (continuous_apply a))

instance locallyCompact_herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR R σ n) :=
  (isClosed_HermR R σ n).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Gen

section Arch

variable (F : Type) [Field F] [NumberField F]

instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_Ainf : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

end Arch

end PI.VolStabW
