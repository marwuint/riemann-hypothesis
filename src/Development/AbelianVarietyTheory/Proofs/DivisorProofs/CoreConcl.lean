import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col0 {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def IsIwaHtG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
    ∃ k ∈ levelAll σ J L a, g = p * k) ∧
  ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
    ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def HidaSetting (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧ 4 ≤ n ∧ IsWittFrame σ J X Y ∧
    GlobalTheory.EisLine.IsAdapted σ J X Y L a ∧ IsIwaHtG σ J (col0 X) L a h

end GlobalTheory.EisRes

end
