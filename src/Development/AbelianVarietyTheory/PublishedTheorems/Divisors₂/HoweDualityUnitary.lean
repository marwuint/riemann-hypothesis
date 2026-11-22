import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.Published

section Local

variable {G H Y V T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup T]
  [Module ℂ T]

def IsLeftHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) : Prop :=
  ∀ (g : G) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, 1) φ → f φ₁ = π g (f φ)

def IsPairHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (τ : Representation ℂ H T)
    (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  ∀ (g : G) (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, h) φ → f φ₁ = TensorProduct.map (π g) (τ h) (f φ)

def IsBigTheta (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (Θ : Representation ℂ H T)
    (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  IsPairHom om π Θ p ∧ Function.Surjective p ∧ ∀ φ, p φ = 0 ↔ ∀ f, IsLeftHom om π f → f φ = 0

def HoweDualityFor [TopologicalSpace G] [TopologicalSpace H] (om : G × H →* Module.End ℂ (Y → ℂ)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π →
    (∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T) (Θ : Representation ℂ H T) (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T),
      IsBigTheta om π Θ p ∧ GlobalTheory.PRep.IsSmooth Θ ∧ IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule ∧
        ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N') ∧
    ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ H T), τ.IsIrreducible → GlobalTheory.PRep.IsSmooth τ →
      ∀ f : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f → f ≠ 0 →
        (∀ f' : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f' → ∃ a : ℂ, f' = a • f) ∧
        ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ G V'), π'.IsIrreducible →
          GlobalTheory.PRep.IsAdmissible π' → ∀ f' : SB Y →ₗ[ℂ] V' ⊗[ℂ] T, IsPairHom om π' τ f' → f' ≠ 0 → Nonempty (π.Equiv π')

end Local

def HoweDualityUnitary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E),
    IsHerm c JA → ξ ≠ 0 → (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ χA χB : Eˣ →* Circle, Continuous χA → Continuous χB → ResEtaPow (R := k) ⊥ χA n → ResEtaPow (R := k) ⊥ χB d →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsUWeilPair c (sbClass k) ψ ξ JA JB co χA χB om →
    HoweDualityFor om ∧ HoweDualityFor (om.comp (MulEquiv.prodComm (M := UG c JB) (N := UG c JA)).toMonoidHom)

def ThetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F) (N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)) : Prop :=
  augAt om v ≤ N ∧ N ≤ SB _ ∧
    ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N

end GlobalTheory.Published

end
