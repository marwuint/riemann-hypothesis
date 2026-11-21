import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain

noncomputable section

structure HermitianNorms (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module (𝓞 K) V] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ V)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ V),
    (form (conjugate σ)).inner (conjMap σ V x) (conjMap σ V y) = starRingEnd ℂ ((form σ).inner x y)

structure FullLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where

  carrier : Submodule (𝓞 K) V
  fg : carrier.FG
  span_eq : Submodule.span K (carrier : Set V) = ⊤

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in

theorem isTorsionFree_of_vectorSpace : Module.IsTorsionFree (𝓞 K) V :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x hax ↦ by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have ha' : (a : K) ≠ 0 := by exact_mod_cast ha
      have : (a : K) • x = 0 := by rw [← hax]; exact algebraMap_smul K a x
      exact (smul_eq_zero.mp this).resolve_left ha'

def HermitianNorms.restrict (N : HermitianNorms K V) (L : Submodule (𝓞 K) V)
    [Module.Finite (𝓞 K) L] [Module.Projective (𝓞 K) L] : HermitianMetric K L where
  form σ := coreComap (N.form σ) (fibreMap σ L.subtype) (fibreMap_injective σ L.injective_subtype)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, N.form_conj]

namespace FullLattice

variable (L : FullLattice K V)

instance : Module.Finite (𝓞 K) L.carrier := Module.Finite.iff_fg.mpr L.fg

instance : Module.Projective (𝓞 K) L.carrier :=
  haveI : Module.IsTorsionFree (𝓞 K) V := isTorsionFree_of_vectorSpace
  projective_of_isTorsionFree _

end FullLattice

def HermitianNorms.bundle (N : HermitianNorms K V) (L : FullLattice K V) : HermitianBundle K :=
  ⟨L.carrier, N.restrict L.carrier⟩

section Local

variable (v : HeightOneSpectrum (𝓞 K))

def toLocal : V →ₗ[K] v.adicCompletion K ⊗[K] V := TensorProduct.mk K (v.adicCompletion K) V 1

def localLattice (L : Submodule (𝓞 K) V) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V) :=
  Submodule.span _ (toLocal v '' (L : Set V))

end Local

end

end GroundTheory.Heights₂.Heights
