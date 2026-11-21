import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

namespace GlobalTheory.Core.Rk.NSing

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def pairM {n : ℕ} (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ b, S a b * T b a)

def starM (σ : E →ₐ[F] E) {m n : ℕ} (g : Matrix (Fin m) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin m) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ

variable [TopologicalSpace R] (χ : R → ℂ) (σ : E →ₐ[F] E)

end Ring

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}

def hermInf (S : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨Matrix.of fun a c => Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def hermV (v : HeightOneSpectrum (𝓞 F)) (S : HermR (AF F) σ n) : HermR (Fv F v) σ n :=
  ⟨Matrix.of fun a c => GlobalTheory.GaugeEx.prV v (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR, GlobalTheory.GaugeEx.prV]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def LocInv (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) (lam : HermR R σ n → ℝ) : Prop :=
  ∃ N ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)), ∀ m ∈ N, ∀ S S' : HermR R σ n,
    S'.1 = m * S.1 * starM R σ m → lam S' = lam S

def IsIdxHgt (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : HermR (Fv F v) σ n → ℝ) : Prop :=
  ∀ μ : Measure (Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ {y | ∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v} = 1 →
    ∀ S, lam S = μ.real {y | (∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v) ∧ ∀ i, (S.1 *ᵥ y) i ∈ GlobalTheory.GaugeEx.intV b v}

structure IsHgt (b : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (lam : HermR (AF F) σ n → ℝ)
    (li : HermR (Ainf F) σ n → ℝ) (lv : ∀ v, HermR (Fv F v) σ n → ℝ) (x₀ : ℝ) : Prop where

  prod : ∀ S, lam S = li (hermInf σ S) * ∏ᶠ v, lv v (hermV σ v S)

  inf : Continuous li ∧ ∀ S, 0 < li S

  fin : ∀ v, Continuous (lv v) ∧ ∀ S, 0 < lv v S

  poly : ∃ (C : ℝ) (N : ℕ), ∀ S, li S ≤ C * (1 + sizeTup b S.1) ^ N ∧ (li S)⁻¹ ≤ C * (1 + sizeTup b S.1) ^ N

  inv : ∀ v, LocInv (Fv F v) σ (lv v)

  unr : ∀ᶠ v in cofinite, IsIdxHgt σ b v (lv v)

  int : ∀ x : ℝ, x₀ < x → Integrable (fun S => lam S ^ x) ν

structure IsBump (b : Module.Basis (Fin d) F E) (χ : Ainf F → ℂ) (ν : Measure (HermR (Ainf F) σ n))
    (β : HermR (Ainf F) σ n → ℝ) : Prop where

  cont : Continuous β

  nonneg : ∀ S, 0 ≤ β S

  cpt : HasCompactSupport β

  mass : ∫ S, β S ∂ν = 1

  dec : ∀ N : ℕ, Integrable (fun S : HermR (Ainf F) σ n =>
    ‖∫ T, (β T : ℂ) * conj (χ (pairM (Ainf F) S.1 T.1)) ∂ν‖ * (1 + sizeTup b S.1) ^ N) ν

end Adelic

end GlobalTheory.Core.Rk.NSing

end
