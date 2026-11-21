import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbedding
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLeftMulMatrixOfCommuteCompanion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparable
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem gl_lc_td (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] [IsUltrametricDist F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ TotallyDisconnectedSpace (GL (Fin r) F) := by
  refine ⟨?_, ?_⟩
  · haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
    exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) F)).locallyCompactSpace
  · haveI : TotallyDisconnectedSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (TotallyDisconnectedSpace (Fin r → Fin r → F))
    exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_cutoff_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  intro F E _ _ _ _ _ A r τ p hG lam μK hμ f' hf'
  haveI := (Unram.lcF (F := F) (E := E))
  haveI := (Unram.ultraF (F := F) (E := E))
  obtain ⟨hlc, htd⟩ := gl_lc_td F r
  obtain ⟨hB, hH, -⟩ := _root_.GlobalTheory.JR.LinDesc.unitsMeas_isHaar F E A μK hμ
  have hZ : IsCompact (Prod.fst '' tsupport f') := hf'.2.isCompact.image continuous_fst
  obtain ⟨C, hC, hCg⟩ := (_root_.GlobalTheory.OrbCpt.orbit_cpt F E r).1 (companion p) (_root_.GlobalTheory.JR.LinDesc.charpoly_companion_separable F E A r τ p hG) _ hZ
  obtain ⟨α, h1, h2, h3, h4⟩ := _root_.GlobalTheory.CutOff.exists_cutoff (GL (Fin r) F) A.Kˣ (LinDesc.tm A hG)
    (_root_.GlobalTheory.JR.LinDesc.tm_isClosedEmbedding F E A r τ p hG) (LinDesc.unitsMeas A μK) C hC
  refine ⟨α, h1, h2, h3, ?_⟩
  rintro g ⟨v, w, hne⟩ s₀
  have hmem : (g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈
      Prod.fst '' tsupport f' := ⟨(_, v, w, lam), subset_tsupport _ (Function.mem_support.2 hne), rfl⟩
  obtain ⟨c, hc, t, ht, rfl⟩ := hCg g hmem
  obtain ⟨t₁, rfl⟩ := _root_.GlobalTheory.JR.LinDesc.centr F E A r τ p hG t ht
  have := h4 c hc (t₁ * s₀)
  simpa [map_mul, mul_assoc] using this

end GlobalTheory.JR.LinDesc
