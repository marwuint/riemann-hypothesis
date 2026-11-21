import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerLeviDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_leviOne {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {g : GAd σ J} : g ∈ leviOne σ J X Y S ↔ ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols Y k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols X k) ((GlobalTheory.Doubling.absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
  simp only [leviOne, levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
  exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩,
    fun k hk => (h k hk).2.2⟩⟩

end GlobalTheory.LeviSplit
