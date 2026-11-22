import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.LatticeOfLocalisationsHyps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt

universe u v

noncomputable section

set_option linter.unusedSectionVars false

namespace LocalChangeEq

def AAt (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : Prop :=
  ∀ (Nm : HermitianNorms K V) (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    {v | g v ≠ 1}.Finite →
    (∀ v, (Heights.localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' Heights.localLattice v M₁.carrier) →
      (Nm.bundle M₂).deg = (Nm.bundle M₁).deg +
        (∑ᶠ v, Real.log ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖) /
          Module.finrank ℚ K

variable {K : Type*} [Field K] [NumberField K]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))

def intEquiv : V ≃ₗ[𝓞 K] (Fin r → K) := φ.restrictScalars (𝓞 K)

def fibreCoord (σ : K →+* ℂ) : Fibre σ V →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fibreMap σ (intEquiv φ).toLinearMap

variable (v : HeightOneSpectrum (𝓞 K))

def localEquiv : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  (LinearEquiv.baseChange K (v.adicCompletion K) V (Fin r → K) φ).trans
    (TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) (Fin r))

def glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (Matrix.toLin' ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
      Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

theorem glEquiv_apply (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K))
    (x : Fin r → v.adicCompletion K) : glEquiv v g x = glMap v g x := rfl

end LocalChangeEq

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
