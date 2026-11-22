import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

set_option maxHeartbeats 1000000 in

theorem fibSF_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibSF σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ UsetF σ J t B₀)ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ BsetF R σ B₀
  swap
  · simp [fibSF, hS]
  obtain ⟨m₀, D₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  have hH := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).2
  have hker₁ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨hsf', -, -, hfib'⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hsf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hα : IsUnit α := by
    have hu : α * (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) = 1 := by
      simp [α, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
    exact IsUnit.of_mul_eq_one _ hu
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hopen := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ D.hCM R D.hR (n + 1) (M + 1)
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet.inter
      hopen.measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∧
        LinearIndependent (R ⊗[F] E) (f p) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    refine ⟨?_, ?_⟩
    · change gramR R σ (blockOne (algebraMap F E t) J)
        (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
      rw [hpres]
      exact hcoord S p.2 hS hp.1
    · exact (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff F E R σ (M + 1) (n + 1) _ (s p.1) (vec α c p.2)).2
        ((GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n α hα c p.2).2 hp.2)
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      UsetF σ J t B₀)ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS.1, ⟨⟨S, hS, (Set.mem_singleton_iff.1 hxS.1).symm⟩, hxS.2⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibSF
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.StageF
