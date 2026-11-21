import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.VacLinW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem symp_eq_zero_of_comp (hcm : IsCMExt F E σ) {v : Pl F} (s : E →ₐ[F] Fv F v)
    {x y : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x) (hx0 : x.map (piW (s.comp σ)) = 0)
    (hy0 : y.map (piW (s.comp σ)) = 0) (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) : symp (cA σ) ξ JA JB x y = 0 := by
  set z := hTens (cA σ) JA JB x y with hz
  have hat : At (evFin F v) z := by
    intro c hc
    have hij : ∀ i j, c • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx c hc) i) j
      simpa using this
    simp only [hz, hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have hx' : ∀ i j, piW (s.comp σ) (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx0 i) j
  have hy' : ∀ i j, piW (s.comp σ) (y i j) = 0 := fun i j => by simpa using congrFun (congrFun hy0 i) j
  have h1 : piW s z = 0 := by
    simp only [hz, hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, hy', mul_zero, Finset.sum_const_zero]
  have h2 : piW (s.comp σ) z = 0 := by
    simp only [hz, hTens, map_sum, map_mul, hx', zero_mul, Finset.sum_const_zero]
  have : z = 0 := GlobalTheory.VacIso.eq_zero_of_at_split hcm s hat h1 h2
  simp only [symp, ← hz, this, mul_zero, map_zero]

theorem symp_add_right (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (cA σ) ξ JA JB x (y + y') = symp (cA σ) ξ JA JB x y + symp (cA σ) ξ JA JB x y' := by
  simp only [symp, hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem isLin_smul {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    {π₁ π₀ : AE F E →+* Fv F v} {co : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v)}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} (h : M.IsLin ψ π₁ π₀ co ι)
    {z : ℂ} (hz : z ≠ 0) : M.IsLin ψ π₁ π₀ co (z • ι) where
  bij := by
    refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
    · simp only [LinearMap.smul_apply]; exact Submodule.smul_mem _ z (h.bij.mapsTo hφ)
    · simp only [LinearMap.smul_apply] at e
      exact h.bij.injOn hφ hφ' (smul_right_injective _ hz e)
    · obtain ⟨φ, hφ, e⟩ := h.bij.surjOn (Submodule.smul_mem _ z⁻¹ hg)
      refine ⟨φ, hφ, ?_⟩
      simp only [LinearMap.smul_apply, e, smul_smul, mul_inv_cancel₀ hz, one_smul]
  trans := fun u hu h0 φ hφ φ₁ hφ₁ hA Y => by
    simp only [LinearMap.smul_apply, Pi.smul_apply, h.trans u hu h0 φ hφ φ₁ hφ₁ hA Y]
  mult := fun u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0 => by
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h.mult u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0]
    ring

end GlobalTheory.VacLinW
