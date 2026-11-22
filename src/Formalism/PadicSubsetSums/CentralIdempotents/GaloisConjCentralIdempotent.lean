import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent

open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def glEquiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv

variable {K} in

def transp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (τ : FDRep ℂ (GL ι K)) : FDRep ℂ (GL κ K) :=
  FDRep.of (τ.ρ.comp (glEquiv K e).symm.toMonoidHom)

structure LabelMap (C : LabelConv K) where
  lab : ∀ d : ℕ, FDRep ℂ (GL (Fin d) K) → K[X]
  lab_iso : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), Nonempty (τ ≅ τ') → lab d τ = lab d τ'
  lab_spec : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    (lab d τ).Monic ∧ Irreducible (lab d τ) ∧ lab d τ ≠ X ∧ (lab d τ).natDegree = d
  lab_inj : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' → lab d τ = lab d τ' → Nonempty (τ ≅ τ')
  lab_one : ∀ (τ : FDRep ℂ (GL (Fin 1) K)) (x : K), Simple τ → x ≠ 0 →
    (∀ (γ : GL (Fin 1) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m) →
    lab 1 τ = X - Polynomial.C x

variable {K} in

def LabelMapEquivariant {C : LabelConv K} (O : LabelMap K C) : Prop :=
  (∀ (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ τ τ' : FDRep ℂ (GL (Fin d) K), 1 ≤ d → Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) →
      rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· ^ a)) ∧
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' →
    (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (·⁻¹)

variable {K} {C : LabelConv K}

def labO (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] (σ : FDRep ℂ (GL κ K)) : K[X] :=
  O.lab (Fintype.card κ) (transp (Fintype.equivFin κ) σ)

def HasLabelO (O : LabelMap K C) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, labO O (lam c)

def twoBlock (n a : ℕ) : Fin n → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

section BaseChange
variable {Γ : Type} [Group Γ]

def bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) : Representation ℂ Γ (Fin (Module.finrank ℂ V) → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ ≃ₐ[ℂ]
      ((Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))).toRingEquiv.toMonoidHom.comp
    ((σ.toRingHom.mapMatrix : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →+*
        Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toRingEquiv.toMonoidHom.comp ρ))

def bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : FDRep ℂ Γ := FDRep.of (bcRepr σ τ.ρ)

theorem trace_bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) (γ : Γ) :
    LinearMap.trace ℂ _ (bcRepr σ ρ γ) = σ (LinearMap.trace ℂ V (ρ γ)) := by
  have h1 : bcRepr σ ρ γ = Matrix.toLin' (σ.toRingHom.mapMatrix
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ γ))) := rfl
  rw [h1, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ γ)]
  simp [Matrix.trace, map_sum]

theorem finrank_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) :
    Module.finrank ℂ (bc σ τ) = Module.finrank ℂ τ := by
  exact Module.finrank_fin_fun ℂ

theorem zIdem_coeff [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ) :
    (zIdem τ).coeff γ = (Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹) := by
  classical
  unfold zIdem
  simp [MonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply, MonoidAlgebra.single]
end BaseChange

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def BcZIdem : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ),
    σ ((zIdem τ).coeff γ) = (zIdem (bc σ τ)).coeff γ

theorem galoisConjCentralIdempotent : BcZIdem := by
  intro Γ _ _ σ τ γ
  have h : LinearMap.trace ℂ (bc σ τ) ((bc σ τ).ρ γ⁻¹) = σ (LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :=
    trace_bcRepr σ τ.ρ γ⁻¹
  rw [zIdem_coeff, zIdem_coeff, finrank_bc, h, map_mul, map_div₀, map_natCast, map_natCast]

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

end Formalism.IrreducibleCountingLemmas.TYPES
