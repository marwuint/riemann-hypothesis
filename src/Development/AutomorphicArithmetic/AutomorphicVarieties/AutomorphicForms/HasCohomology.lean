import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def regFun : Subalgebra ℂ (GL (Fin a) (Rinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ v i j, f = fun y => ((y.val i j v : ℝ) : ℂ)} ∪ {f | ∃ v, f = fun y => ((y.val.det v : ℝ) : ℂ)⁻¹})

variable (E a) in

structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Rinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

open Classical in

def extGL (f : GL (Fin a) (Rinf E) → ℂ) (x : Lie E a) : ℂ := if h : IsUnit (Matrix.of x) then f h.unit else 0

def AlgRep.dmat (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a) X
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp

open Classical in

def AlgRep.HasInfChar (Ξ : AlgRep E a) (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => Ξ.dmat (toL (Matrix.single i j (Pi.single v 1)))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

variable [IsTotallyReal E]

end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

omit [IsTotallyComplex E] in

def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)

omit [IsTotallyComplex E] in

def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
