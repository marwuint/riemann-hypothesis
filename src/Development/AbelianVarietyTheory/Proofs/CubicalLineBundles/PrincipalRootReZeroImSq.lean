import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ReEqZeroAndImSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

noncomputable section

namespace GlobalTheory.PrincipalDatum

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem coe_add' (a b : 𝓞 E) : ((a + b : 𝓞 E) : E) = a + b := rfl

omit [NumberField E] in
theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = a * b := rfl

theorem exists_clear (𝔞 : Submodule (𝓞 E) E) (h : 𝔞.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ ψ : 𝔞 →ₗ[𝓞 E] 𝓞 E, ∀ x, (ψ x : E) = N * (x : E) := by
  obtain ⟨a, ⟨N, hN, rfl⟩, ha⟩ :=
    FractionalIdeal.isFractional_of_fg (S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) h
  choose f hf using ha
  have hf' : ∀ x : 𝔞, ((f x x.2 : 𝓞 E) : E) = N * (x : E) := fun x => by
    have := hf x x.2
    rw [Algebra.smul_def] at this
    simpa using this
  refine ⟨N, nonZeroDivisors.ne_zero hN, ⟨⟨fun x => f x x.2, fun x y => ?_⟩, fun c x => ?_⟩, hf'⟩
  · apply RingOfIntegers.ext
    rw [coe_add', hf', hf', hf', Submodule.coe_add, mul_add]
  · apply RingOfIntegers.ext
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [coe_mul', hf', hf', Submodule.coe_smul, Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring

def act (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (a : 𝓞 E) : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M :=
  (DistribSMul.toLinearMap ℤ M a).baseChange ℝ

section Act

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M]

omit [NumberField E] in
@[simp] theorem act_tmul (a : 𝓞 E) (r : ℝ) (x : M) : act M a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl

end Act

variable [IsCMField E]

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ^ 2 = H.d := by
  first
  | exact @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | (apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq ..)

end GlobalTheory.PrincipalDatum
