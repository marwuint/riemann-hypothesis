import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolume
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicHaarDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicQuotientMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainVolume
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_haar_fundamentalDomain : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hU hΓ₁ hΓ μ₁ _ 𝓕₁ h𝓕₁ hfin hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]; exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨D, hDm, hDu, hD⟩ := _root_.GlobalTheory.CompanionTheory.SplitExtLat.exists_borel_section_ker P G₁ ι π hι hπ hπι Γ hU hK
  let ν : Measure π.ker := Measure.haar
  obtain ⟨hνF, hν0, hνfin⟩ := hD ν
  obtain ⟨δ, hδm, hδΓ, hδ⟩ := _root_.GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν D hDm hνF hν0 hνfin
  have hδ1 := _root_.GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin δ hδm hδΓ
  have hmap : ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν := by
    intro u; rw [hδ u, hδ1 u, one_smul]
  have hH := _root_.GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo P G₁ ι π hι hπ hπι ν μ₁ hmap
  obtain ⟨hnull, hint⟩ := _root_.GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod P G₁ ι π hι hπ hπι ν μ₁ D 𝓕₁ hDm h𝓕₁.nullMeasurableSet
  have hcov := _root_.GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν μ₁ D 𝓕₁ hDu h𝓕₁
  have hdis := _root_.GlobalTheory.CompanionTheory.SplitExtLat.aedisjoint_smul_image_prod P G₁ ι π hι hπ hπι Γ Γ₁ hΓ ν μ₁ D 𝓕₁ hDu h𝓕₁
  refine ⟨ν, D, _, _, inferInstance, hνF, hν0, hνfin, hH,
    IsFundamentalDomain.mk'' hnull hcov hdis (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving), ?_, hint⟩
  have h1 := hint (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, setLIntegral_one] at h1
  rw [h1]
  exact ENNReal.mul_lt_top hνfin hfin

end GlobalTheory.CompanionTheory.SplitExtLat
