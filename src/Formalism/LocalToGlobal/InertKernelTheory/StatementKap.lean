import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def KapInert : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l], B.KappaAt l ι

def KappaFirstKernelHypothesis : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l],
    ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ l ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ‖ι e‖ = 1 ∧
      B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ B.cq (matH (hOne B.L D.what₂.Tau))) B.lamM ∧
      tens4 B.thMM = e • kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g

end Formalism.L2.KerInert
