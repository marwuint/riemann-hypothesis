import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem repr_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]

end Coord

section Box

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_box (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v, IsCompact (C v))
    (hS : ∀ v, v ∉ S → C v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    IsCompact {y : Af F | ∀ v, y v ∈ C v} := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF
  have hcoe := RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)
  let K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) :=
    {x | ∀ v, x v ∈ C v}
  have hK : IsCompact K := by
    rw [hcoe.isCompact_iff]
    have : (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hx
        refine ⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩,
          fun v => hx v (Set.mem_univ v), rfl⟩
    rw [this]
    exact isCompact_univ_pi hC
  have himg := hK.image hemb.continuous
  have hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v :=
        Filter.eventually_principal.2 fun v hv => hS v hv (hy v)
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      exact hx v
  rw [hset]
  exact himg

end Box

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
