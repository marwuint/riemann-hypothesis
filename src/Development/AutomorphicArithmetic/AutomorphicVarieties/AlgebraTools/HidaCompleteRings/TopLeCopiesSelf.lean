import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Alg

variable {k G V N : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup N] [Module k N]

def Stab (ρ : Representation k G V) (W : Submodule k V) : Prop := ∀ g, ∀ v ∈ W, ρ g v ∈ W

abbrev Into (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Type :=
  {f : N →ₗ[k] V // (∀ g v, f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y}

def copies (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Submodule k V :=
  ⨆ f : Into ρ Y σ, LinearMap.range f.1

theorem Stab.comp {ρ : Representation k G V} {W : Submodule k V} (h : Stab ρ W) {H : Type} [Group H] (j : H →* G) :
    Stab (ρ.comp j) W := fun x => h (j x)

def piRep (ρ : Representation k G V) (ι : Type) : Representation k G (ι → V) where
  toFun g := LinearMap.compLeft (ρ g) ι
  map_one' := by ext1 F; simp; rfl
  map_mul' a b := by ext1 F; simp; rfl

@[simp] theorem piRep_apply (ρ : Representation k G V) (ι : Type) (g : G) (F : ι → V) (i : ι) :
    piRep ρ ι g F i = ρ g (F i) := rfl

end Alg

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
