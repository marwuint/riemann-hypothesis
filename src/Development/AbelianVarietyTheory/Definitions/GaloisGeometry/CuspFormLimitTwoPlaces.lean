import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def SeedWtU : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), (Qbar l ≃+* ℂ) →
    HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Submodule ℂ (UA E a → ℂ) → Prop

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def OverPl (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x ∈ w.asIdeal, ‖ι.symm (τ (x : E))‖ < 1

def SameWtAt (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SameWtOff (ι : Qbar l ≃+* ℂ) (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (∀ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u → Apart u w₀ ∧ Apart u v') →
    ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

theorem sameWtAt_of_off (ι : Qbar l ≃+* ℂ) {w₀ v' w : HeightOneSpectrum (𝓞 E)} {U U' : Submodule ℂ (UA E a → ℂ)}
    (h : SameWtOff ι w₀ v' U U') (hw : ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ u, OverPl ι τ u → u = w)
    (h₀ : Apart w w₀) (h' : Apart w v') : SameWtAt ι w U U' :=
  fun τ hτ lam => h τ (fun u hu => by rw [hw τ hτ u hu]; exact ⟨h₀, h'⟩) lam

end GlobalTheory.CongL

end
