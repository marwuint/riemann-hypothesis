import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
