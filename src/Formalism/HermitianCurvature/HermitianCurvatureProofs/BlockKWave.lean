import Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem prod_ofFn_map {K : ℕ} (f : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn f).map g).prod = ∏ b, g (f b) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

section blockK

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem sW_eq (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) :
    sW S j l = Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l := rfl

end blockK

end

end Formalism.FourierDecayAlt.P.PBL
