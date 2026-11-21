import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

abbrev HCo (a : ℕ) : Type := (Fin a → ℝ) × ({p : Fin a × Fin a // p.1 < p.2} → ℂ)

def hOf {a : ℕ} (t : HCo a) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  if h : i < j then t.2 ⟨(i, j), h⟩ else if h' : j < i then star (t.2 ⟨(j, i), h'⟩) else (t.1 i : ℂ)

abbrev Tup (k r a : ℕ) : Type := Fin (2 * r + k + 1) → Fin a → ℂ

def gramC {k r a : ℕ} (X : Tup k r a) : Matrix (Fin a) (Fin a) ℂ :=
  (Matrix.of X)ᴴ * Hpk k r * Matrix.of X

def DefPerp {k r a : ℕ} (X : Tup k r a) : Prop :=
  (gramC X).det ≠ 0 ∧ PosOnPerp (Hpk k r) (Matrix.of X)

def DefGram (k r a : ℕ) : Set (HCo a) := {t | ∃ X : Tup k r a, gramC X = hOf t ∧ DefPerp X}

def IsGramConst (k r a : ℕ) (μ : Measure (Mt k r)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ Φ : Tup k r a → ℝ≥0∞, Measurable Φ → ∀ s : HCo a → Tup k r a,
    (∀ t ∈ DefGram k r a, gramC (s t) = hOf t) →
    (2 : ℝ≥0∞) ^ ((2 * r + k + 1) * a) * ∫⁻ X in {X | DefPerp X}, Φ X =
      (2 : ℝ≥0∞) ^ (a * (a - 1) / 2) * ∫⁻ t in DefGram k r a,
        ENNReal.ofReal (C * ‖(hOf t).det‖ ^ (2 * r + k + 1 - a)) *
          ∫⁻ g, Φ (Matrix.of.symm (Matrix.of g * Matrix.of (s t))) ∂μ

section Glob

variable {E : Type} [Field E] [NumberField E]

def tupLat {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (P : Matrix (Fin n) (Fin a) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin a) (x : E), x ∈ 𝔞 b ∧ v = x • fun i => P i b}

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

def difAt (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^
    (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))

def StdAt (v : HeightOneSpectrum (𝓞 F)) (ψ : Fv F v → ℂ) : Prop :=
  ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), x * algebraMap F (Fv F v) (d : F) ∈ v.adicCompletionIntegers F

def IsStdChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) ∧
    ∀ v, StdAt v (psiV F ψ v)

variable (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)

def IsModelAt (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ w, (A w)ᴴ * Hpk k r * A w = J.map w.embedding

end Glob

end GlobalTheory.SnMass
