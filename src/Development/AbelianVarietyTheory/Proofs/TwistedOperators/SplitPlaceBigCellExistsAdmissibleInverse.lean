import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeepsLatticeAtPlaceOfIntegralLocalBasisConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInverses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleLiftSplitPlaceConjugatePair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAtSplitPlaceLocalBasesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBlocksLeftInverseIsUnitDetSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlace

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitPlaceBigCell

theorem splitPlace_bigCell_exists_admissible_inverse : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro hLoc F E _ _ _ _ _ σ d W v hskew h2 π₁ π₂ b₁ b₂ hd hSx g hg
  obtain ⟨hc₁, hc₂, ha₁, ha₂, hinj, hsurj, hlat⟩ := hd
  obtain ⟨S, hSdet, hS⟩ := hSx
  obtain ⟨k11, k12, k21, k22, k11', k12', k21', k22'⟩ := _root_.GlobalTheory.DblVac.KD_blocks_keep σ W v g hg
  have I := fun A hA => _root_.GlobalTheory.IntKeepConj.conj_integral W v π₁ π₂ b₁ b₂ hlat hsurj A hA
  have hinv : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := g.1.inv_mul
  obtain ⟨G₁, hG₁, hG₁u⟩ := _root_.GlobalTheory.integralBlocks_leftInverse_isUnit_det v π₁ b₁ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).1 (I _ k12).1 (I _ k21).1 (I _ k22).1 (I _ k11').1 (I _ k12').1 (I _ k21').1 (I _ k22').1
  obtain ⟨G₂, hG₂, -⟩ := _root_.GlobalTheory.integralBlocks_leftInverse_isUnit_det v π₂ b₂ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).2 (I _ k12).2 (I _ k21).2 (I _ k22).2 (I _ k11').2 (I _ k12').2 (I _ k21').2 (I _ k22').2
  have hU := GlobalTheory.T.unitary_at_splitPlace_localBases σ W v π₁ π₂ b₁ b₂ hc₁ g
  have e : ∀ {m n o : Type} [Fintype n] (A : Matrix m n (v.adicCompletionIntegers F))
      (B : Matrix n o (v.adicCompletionIntegers F)),
      (A * B).map (fun x => (x : Fv F v)) = A.map (fun x => (x : Fv F v)) * B.map (fun x => (x : Fv F v)) :=
    fun A B => Matrix.map_mul (f := (v.adicCompletionIntegers F).subtype)
  have hUO : G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) := by
    apply Matrix.map_injective (f := fun x : v.adicCompletionIntegers F => (x : Fv F v)) Subtype.coe_injective
    beta_reduce
    have en : (-S).map (fun x => (x : Fv F v)) = -(S.map (fun x => (x : Fv F v))) := by ext i j; rfl
    have ez : (0 : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)).map (fun x => (x : Fv F v)) = 0 := by
      ext i j; rfl
    rw [e, e, Matrix.transpose_map, Matrix.fromBlocks_map, en, ez, hG₁, hG₂, hS]
    exact hU
  obtain ⟨X₁, X₂, hX, hP₁, hP₂⟩ := hLoc h2 S hSdet G₁ G₂ hG₁u hUO
  obtain ⟨Y, hYat, hY₁, hY₂, hYadm⟩ :=
    _root_.GlobalTheory.AdmLift.exists_admissible_lift σ W v hskew π₁ π₂ b₁ b₂ hc₁ hc₂ hinj hsurj S hS X₁ X₂ hX
  obtain ⟨N₁, hN₁, hN₁i⟩ := _root_.GlobalTheory.Twist.halfBlockSum_inv_conj_integral v π₁ b₁ ha₁ (GlobalTheory.DblVac.matD g) G₁ hG₁ X₁ hP₁ Y hY₁
  obtain ⟨N₂, hN₂, hN₂i⟩ := _root_.GlobalTheory.Twist.halfBlockSum_inv_conj_integral v π₂ b₂ ha₂ (GlobalTheory.DblVac.matD g) G₂ hG₂ X₂ hP₂ Y hY₂
  have hK := _root_.GlobalTheory.TwistBlockK.atK_sub_one v (GlobalTheory.DblVac.matD g) Y hg.1 hYat
  obtain ⟨M, hMK, hM₁, hM₂⟩ := _root_.GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift v π₁ π₂ hinj hsurj _ hK N₁ N₂ hN₁ hN₂
  have hYi : ∀ (b : GL (Fin d) (Fv F v)) (X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)),
      ∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F := by
    intro b X i j
    have : ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v)) = X.map (fun x => (x : Fv F v)) := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact (X i j).2
  refine ⟨Y, hYat, _root_.GlobalTheory.KeepInt.keepLat W v π₁ π₂ b₁ b₂ hlat Y ?_ ?_, hYadm, M, hMK,
    _root_.GlobalTheory.KeepInt.keepLat W v π₁ π₂ b₁ b₂ hlat M ?_ ?_⟩
  · rw [hY₁]; exact hYi b₁ X₁
  · rw [hY₂]; exact hYi b₂ X₂
  · rw [hM₁]; exact hN₁i
  · rw [hM₂]; exact hN₂i

end GlobalTheory.SplitPlaceBigCell
