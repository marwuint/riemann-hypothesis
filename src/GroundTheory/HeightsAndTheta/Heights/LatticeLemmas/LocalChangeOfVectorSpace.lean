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

theorem coordMap_coordInv (r : ℕ) (σ : K →+* ℂ) (w : Fin r → ℂ) :
    coordMap r σ (coordInv σ w) = w := by
  funext j
  simp only [coordInv, map_sum, Finset.sum_apply, coordMap_tmul, AlgEquiv.symm_apply_apply,
    Pi.single_apply]
  simp

theorem coordMap_conjMap (r : ℕ) (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordMap r (conjugate σ) (conjMap σ (Fin r → K) t) = star (coordMap r σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ l) i = starRingEnd ℂ (coordMap r σ (z ⊗ₜ l) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))

def intEquiv : V ≃ₗ[𝓞 K] (Fin r → K) := φ.restrictScalars (𝓞 K)

def fibreCoord (σ : K →+* ℂ) : Fibre σ V →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fibreMap σ (intEquiv φ).toLinearMap

theorem fibreCoord_bijective (σ : K →+* ℂ) : Function.Bijective (fibreCoord φ σ) := by
  refine ⟨(coordMap_injective σ).comp (fibreMap_injective σ (intEquiv φ).injective), ?_⟩
  intro w
  obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (intEquiv φ).surjective (coordInv σ w)
  refine ⟨t, ?_⟩
  show coordMap r σ (((intEquiv φ).toLinearMap).lTensor (ComplexAt σ) t) = w
  rw [ht, coordMap_coordInv]

theorem fibreCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ V) :
    fibreCoord φ (conjugate σ) (conjMap σ V x) = star (fibreCoord φ σ x) := by
  simp only [fibreCoord, LinearMap.comp_apply]
  rw [← conjMap_fibreMap, coordMap_conjMap]

def normsOf (H : HermitianSpace K r) : HermitianNorms K V where
  form σ := coreComap (H.form σ) (fibreCoord φ σ) (fibreCoord_bijective φ σ).1
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, fibreCoord_conjMap, fibreCoord_conjMap, H.form_conj]

theorem normsOf_inner (H : HermitianSpace K r) (σ : K →+* ℂ) (x y : V) :
    ((normsOf φ H).form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)) := rfl

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
