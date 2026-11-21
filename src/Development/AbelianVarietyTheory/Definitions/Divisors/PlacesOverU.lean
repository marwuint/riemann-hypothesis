import Mathlib

noncomputable section

namespace GlobalTheory.UPel.HT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct ComplexConjugate

def HermSig {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (a : ℕ) : Prop :=
  a ≤ n ∧ ∃ P : GL (Fin n) ℂ,
    h = (P : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun k : Fin n => if (k : ℕ) < a then (1 : ℂ) else -1) *
      (P : Matrix (Fin n) (Fin n) ℂ)ᴴ

section Defs

variable (K F : Type) [Field K] [NumberField K] [IsCMField K] [Field F] [NumberField F] [IsCMField F]
  [Algebra K F]

open Classical in

def embOver (σ : K →+* ℂ) : Finset (F →+* ℂ) :=
  Finset.univ.filter fun τ => τ.comp (algebraMap K F) = σ

open Classical in

structure HTDatum (p : ℕ) [Fact p.Prime] where

  quad : Module.finrank ℚ K = 2

  u : HeightOneSpectrum (𝓞 K)

  split : u.asIdeal * u.asIdeal.comap (IsCMField.ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K) =
    Ideal.span {(p : 𝓞 K)}

  split_ne : u.asIdeal.comap (IsCMField.ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K) ≠ u.asIdeal

  w : HeightOneSpectrum (𝓞 F)
  w_over : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 F)) = u.asIdeal

  τ₀ : F →+* ℂ

  B : Type
  [ring : Ring B]
  [starB : StarRing B]
  [algF : Algebra F B]
  [algQ : Algebra ℚ B]
  [central : Algebra.IsCentral F B]
  [simple : IsSimpleRing B]

  n : ℕ
  n_pos : 0 < n
  dim : Module.finrank F B = n ^ 2

  star_F : ∀ a : F, star (algebraMap F B a) = algebraMap F B (IsCMField.complexConj F a)

  pos : ∀ x : B, x ≠ 0 → 0 < LinearMap.trace ℚ B (LinearMap.mulLeft ℚ (x * star x))

  OB : Subalgebra (𝓞 F) B
  OB_fg : (Subalgebra.toSubmodule OB).restrictScalars ℤ |>.FG
  OB_span : Submodule.span ℚ (OB : Set B) = ⊤
  OB_star : ∀ x ∈ OB, star x ∈ OB

  OB_max : ∀ O : Subring B, (OB : Set B) ⊆ O → O.toAddSubgroup.FG →
    ∀ x ∈ O, ∃ m : ℕ, m.Coprime p ∧ (m : B) * x ∈ OB

  splitW : w.adicCompletionIntegers F ⊗[𝓞 F] OB ≃ₐ[w.adicCompletionIntegers F]
    Matrix (Fin n) (Fin n) (w.adicCompletionIntegers F)

  ψ : LinearMap.BilinForm ℚ B
  alt : ∀ x, ψ x x = 0
  adj : ∀ b x y, ψ (b * x) y = ψ x (star b * y)

  sig : ∃ (ρ : (F →+* ℂ) → B →+* Matrix (Fin n) (Fin n) ℂ) (h : (F →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ a, ρ τ (algebraMap F B a) = Matrix.scalar (Fin n) (τ a)) ∧
    (∀ τ b, ρ τ (star b) = (ρ τ b)ᴴ) ∧
    (∀ τ ∈ embOver K F (τ₀.comp (algebraMap K F)), HermSig (h τ) (if τ = τ₀ then 1 else 0)) ∧
    ∀ x y, ((ψ x y : ℚ) : ℝ) =
      ∑ τ ∈ embOver K F (τ₀.comp (algebraMap K F)), 2 * (trace (ρ τ x * h τ * (ρ τ y)ᴴ)).im

  Λ : Submodule ℤ B
  Λ_fg : Λ.FG
  Λ_span : Submodule.span ℚ (Λ : Set B) = ⊤
  Λ_stable : ∀ b ∈ OB, ∀ x ∈ Λ, b * x ∈ Λ

  E : LinearMap.BilinForm ℤ Λ
  E_eq : ∀ x y : Λ, ((E x y : ℤ) : ℚ) = ψ x y

  perfect : Function.Bijective (E.baseChange ℤ_[p])

attribute [instance] HTDatum.ring HTDatum.starB HTDatum.algF HTDatum.algQ HTDatum.central HTDatum.simple

end Defs

namespace HTDatum

variable {K F : Type} [Field K] [NumberField K] [IsCMField K] [Field F] [NumberField F] [IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime] (D : HTDatum K F p)

def Φ : Finset (F →+* ℂ) := embOver K F (D.τ₀.comp (algebraMap K F))

def d : ℕ := Module.finrank ℚ (maximalRealSubfield F)

def placesOverU : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | v.asIdeal.comap (algebraMap (𝓞 K) (𝓞 F)) = D.u.asIdeal}

def IsDivision : Prop := ∀ x : D.B, x ≠ 0 → IsUnit x

def starO (x : D.OB) : D.OB := ⟨star (x : D.B), D.OB_star x x.2⟩

instance : IsScalarTower ℚ F D.B :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance : FiniteDimensional F D.B :=
  Module.finite_of_finrank_pos (by rw [D.dim]; exact pow_pos D.n_pos 2)

end HTDatum

end GlobalTheory.UPel.HT
