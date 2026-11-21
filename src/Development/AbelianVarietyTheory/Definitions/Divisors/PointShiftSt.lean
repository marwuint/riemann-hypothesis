import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable (K) in

def detSpan (m : ℕ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (⋀[K]^m V) :=
  Submodule.span (𝓞 K) {w | ∃ y : Fin m → V, (∀ i, y i ∈ L) ∧ w = exteriorPower.ιMulti K m y}

variable (K) in

def idx (m : ℕ) (L N : Submodule (𝓞 K) V) : Ideal (𝓞 K) := (detSpan K m N).colon (detSpan K m L)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def phiP (a : Fin p) : (X.A true).t.G ⟶ X.B.t.G := X.φ (Sum.inl a)

def phiQ (a : Fin q) : (X.A false).t.G ⟶ X.B.t.G := X.φ (Sum.inr a)

def IsGram (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)) : Prop :=
  (∀ a b, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) ∧
  ∀ a b, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

variable {X} (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
  (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))

def IsDiffs : Prop := (∀ a, FP.IsDiffOf FB (phiP X a) (MP a)) ∧ ∀ a, FQ.IsDiffOf FB (phiQ X a) (MQ a)

def subP (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FP.eigLat (X.A true).t.act τ).map ((MP a).restrictScalars (𝓞 K))

def subQ (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FQ.eigLat (X.A false).t.act τ).map ((MQ a).restrictScalars (𝓞 K))

end GlobalTheory.FlatCM

end
