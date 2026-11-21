import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (D) in

def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

theorem labE_conj (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def ArchLab.flip (A : ArchLab D) : ArchLab D := ⟨A.perm, !A.side⟩

def ArchLab.pos (A : ArchLab D) : ArchLab D := ⟨A.perm, true⟩

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ

variable (D) in

def baseLab : ArchLab D := ⟨Equiv.refl _, true⟩

variable (D) in

def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A

def rl (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : D.what₂.Tau → X := fun ρ => S (A.perm.symm ρ)

theorem rl_base {X : Type*} (S : D.what₂.Tau → X) : rl (baseLab D) S = S := rfl

theorem rl_flip (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : rl A.flip S = rl A S := rfl

theorem rl_pos (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : rl A.pos S = rl A S := rfl

def cv (σ : D.what₂.LL →+* ℂ) {X : Type*} (f : X → D.what₂.LL) : X → ℂ := fun x => σ (f x)

theorem cv_base {X : Type*} (f : X → D.what₂.LL) : cv D.what₂.embLL f = fun x => D.what₂.embLL (f x) := rfl

theorem cv_conj (σ : D.what₂.LL →+* ℂ) {X : Type*} (f : X → D.what₂.LL) :
    cv ((starRingEnd ℂ).comp σ) f = fun x => starRingEnd ℂ (cv σ f x) := rfl

def deltaSig (A : ArchLab D) {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    MvPolynomial (Datum.FVar D m n) ℂ :=
  Datum.delta p q (rl A ap) (rl A am)

theorem deltaSig_base {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    deltaSig (m := m) (n := n) (baseLab D) p q ap am = Datum.delta p q ap am := rfl

end Formalism.IndefR.Conj

end
