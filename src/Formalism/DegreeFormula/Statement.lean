import Mathlib
import Formalism.MoebiusJetDuality.StatementU
import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.DegreeFormula

open Formalism.MJ Formalism.UG

section One

variable {p q : ℕ}

def kapQ (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂

def hQ (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := 1 - zᴴ * z

def hP (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ := 1 - z * zᴴ

end One

section Two

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def DomI (ι : Type) (p q : ℕ) : Set (ι → Matrix (Fin p) (Fin q) ℂ) := {z | ∀ i, z i ∈ hcDom p q}

def UpqI (ι : Type) (p q : ℕ) : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  Subgroup.pi Set.univ (fun _ => Upq p q)

def moebI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => moeb (g i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z i)

def unflat (v : ι × Fin p × Fin q → ℂ) : ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => Matrix.of (fun a b => v (i, a, b))

def flat (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι × Fin p × Fin q → ℂ := fun x => z x.1 x.2.1 x.2.2

def DomFlat (ι : Type) (p q : ℕ) : Set (ι × Fin p × Fin q → ℂ) := {v | unflat v ∈ DomI ι p q}

end Two

section Four

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def muD (ι : Type) [Fintype ι] (p q : ℕ) : Measure (ι × Fin p × Fin q → ℂ) :=
  (volume.restrict (DomFlat ι p q)).withDensity
    (fun v => ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))))

def IsFD (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (F : Set (ι × Fin p × Fin q → ℂ)) : Prop :=
  MeasurableSet F ∧ F ⊆ DomFlat ι p q ∧
    (∀ z ∈ DomI ι p q, ∃ γ ∈ Γ, flat (moebI γ z) ∈ F) ∧
    muD ι p q {v | v ∈ F ∧ ∃ γ ∈ Γ, flat (moebI γ (unflat v)) ∈ F ∧ moebI γ (unflat v) ≠ unflat v} = 0

end Four

section CompanionTheory

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} {p q : ℕ}

def embI (τ : ι → E →+* ℂ) (e : ι → n ≃ Fin p ⊕ Fin q) (P : ι → GL (Fin p ⊕ Fin q) ℂ) :
    GL n E →* (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  MonoidHom.pi (fun i => (MulAut.conj (P i)⁻¹).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map (τ i)).comp
      (Units.map (Matrix.reindexAlgEquiv E E (e i)).toMonoidHom)))

end CompanionTheory

end Formalism.DegreeFormula
