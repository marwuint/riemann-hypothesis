import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeInhabitant

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_fin : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Continuous Φ ∧
    (∀ x, Φ (incA F E x) = algebraMap E _ x) ∧
    ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have := GlobalTheory.HeckeTensorRead.continuous_of_map_integral
    (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P =>
      (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)
  exact this.comp continuous_snd

theorem cA_inc (σ : E →ₐ[F] E) (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) x P) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

end General

end GlobalTheory.HeckeInhabitant
