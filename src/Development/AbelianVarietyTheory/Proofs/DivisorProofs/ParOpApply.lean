import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU

namespace GlobalTheory.WeilEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Impl

variable {a b : ℕ} {JX : Matrix (Fin a) (Fin a) E} {JW : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]

structure Impl (ψ : AddChar (AF F) ℂ) (co : Darboux (sy σ JX JW) κ) (g : UA σ JX × UA σ JW)
    (S : Module.End ℂ ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) g w) (S φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S ∈ (adeleClass F).adm κ
  unit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

theorem actAB_mul (g g' : UA σ JX × UA σ JW) (w : Matrix (Fin a) (Fin b) (AE F E)) :
    actAB (cA σ) (g * g') w = actAB (cA σ) g (actAB (cA σ) g' w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

variable {ψ : AddChar (AF F) ℂ} {co : Darboux (sy σ JX JW) κ}

theorem Impl.mul {g g' : UA σ JX × UA σ JW} {S S' : Module.End ℂ ((κ → AF F) → ℂ)} (h : Impl ψ co g S)
    (h' : Impl ψ co g' S') : Impl ψ co (g * g') (S * S') :=
  ⟨fun φ hφ => h.pres _ (h'.pres φ hφ),
    fun w φ hφ => by
      rw [Module.End.mul_apply, h'.Heisenberg₂ w φ hφ, h.Heisenberg₂ _ _ (h'.pres φ hφ), actAB_mul, Module.End.mul_apply],
    fun l hl => h'.adm _ (h.adm l hl),
    fun μ hμ φ hφ => by rw [Module.End.mul_apply, h.unit μ hμ _ (h'.pres φ hφ), h'.unit μ hμ φ hφ]⟩

end Impl

variable {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

end GlobalTheory.WeilEx

end
