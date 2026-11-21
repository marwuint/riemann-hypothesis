import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

noncomputable section

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]

def coordAt (O : Type) [CommRing O] [Algebra O K] (c : Ideal (OF E)) (σ : E →+* K) : orderC c ⊗[ℤ] O →ₐ[ℤ] K :=
  Algebra.TensorProduct.productMap (σ.comp (orderC c).subtype).toIntAlgHom (algebraMap O K).toIntAlgHom

variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

def eigK (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : Submodule K (K ⊗[O] H) :=
  ⨅ a : orderC c, Module.End.eigenspace ((ρ a).baseChange K) (σ a)

def inK (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] : H →ₗ[O] K ⊗[O] H :=
  TensorProduct.mk O K H 1

def ofF (c : Ideal (OF E)) (a : OF E) : orderC c := ⟨algebraMap (OF E) E a, algebraMap_mem_orderC c a⟩

def IsScaledRestr (D : O) (N : Module.End K (K ⊗[O] H)) (M : Module.End O H) : Prop :=
  ∀ h : H, inK K H (M h) = algebraMap O K D • N (inK K H h)

end Lin

def lPrime (l : ℕ) : ℕ := if l = 2 then 4 else l

def nilPart {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I] (l : ℕ)
    (M : I → Module.End O H) (R : Type) [CommRing R] [Algebra O R] (t : I → R) : Module.End R (R ⊗[O] H) :=
  (lPrime l : R) • ∑ i, t i • (M i).baseChange R

end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
