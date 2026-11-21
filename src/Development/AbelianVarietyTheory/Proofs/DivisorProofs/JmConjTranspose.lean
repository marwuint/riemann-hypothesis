import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Alg

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

theorem isExp_eig {L U : Module.End ℂ V} (hU : IsExp L U) (q : V →ₗ[ℂ] Z) (L0 : Module.End ℂ Z)
    (h : ∀ v, q (L v) = L0 (q v)) {T : V} {μ : ℂ} (hT : L0 (q T) = μ • q T) : q (U T) = Complex.exp μ • q T := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul]
  have hp : ∀ n : ℕ, q ((L ^ n) T) = μ ^ n • q T := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, hT, smul_smul, pow_succ]
  have a := hU T (l ∘ₗ q)
  simp only [LinearMap.comp_apply, hp, map_smul, smul_eq_mul] at a
  have b := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).mul_right (l (q T))
  rw [← Complex.exp_eq_exp_ℂ] at b
  simp only [smul_eq_mul, mul_assoc] at b
  exact a.unique b

end Alg

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d}

variable {B : Base F E} {om : Rep σ Y W} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
  {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {c : InfinitePlace F → ℂ}

theorem acts_unique {T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ f₂ : SInf F (Fin n × Fin d)}
    (h₁ : Acts (evI F) T f f₁) (h₂ : Acts (evI F) T f f₂) : f₁ = f₂ :=
  (Main.i_actslaws F _ f f₁ f₂).2.2.2.1 T h₁ h₂

end Tens

end GlobalTheory.FockBottom
