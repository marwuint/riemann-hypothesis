import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormAevalSubLe

noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

theorem LinApprox.mono {Γ : Type} [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k} {C D : Set (Γ →* GL (Fin a) k)}
    (h : LinApprox r C) (hCD : C ⊆ D) : LinApprox r D := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hCD, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

end GlobalTheory.Cong

end
