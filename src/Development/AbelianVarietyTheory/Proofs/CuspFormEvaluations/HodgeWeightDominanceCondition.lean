import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremalStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingMinorProductHarmonicGenerates
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Classical Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

theorem cof_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first
  | exact @_root_.GlobalTheory.WeightOrderLemmas.main
  | exact _root_.GlobalTheory.WeightOrderLemmas.main
  | (apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightOrderLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightOrderLemmas.main ..)

end GlobalTheory.FrameRead
