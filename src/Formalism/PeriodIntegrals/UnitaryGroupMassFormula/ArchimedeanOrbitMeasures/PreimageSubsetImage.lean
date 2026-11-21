import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousAdelicGL2Det

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

instance instT2SpaceUnitaryPQ (P Q : ℕ) : T2Space (UpqT P Q) := (isClosedEmbedding_mat P Q).isEmbedding.t2Space

section SlopeTestRemainingChoices

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
    funext g
    first
    | (unfold cayInv; rw [dif_pos (cayCand_mem P Q g)])
    | simp [cayInv, cayCand_mem]
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hg' : ∃ X ∈ D0 P Q, g.mat * (1 + 1 - (X : Mat)) = 1 + 1 + (X : Mat) := hg
  obtain ⟨X, -, hgX⟩ := hg'
  have h4 : (g.mat + 1) * (1 + 1 - (X : Mat)) = (4 : ℂ) • (1 : Mat) := by
    rw [add_mul, hgX, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
      one_smul]
    abel
  have hdet : IsUnit (g.mat + 1).det := by
    have h5 := congrArg Matrix.det h4
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h5
    have h' : IsUnit ((g.mat + 1).det * (1 + 1 - (X : Mat)).det) := by
      rw [h5]
      exact (Ne.isUnit (by norm_num : (4 : ℂ) ≠ 0)).pow _
    exact isUnit_of_mul_isUnit_left h'
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    refine (continuousAt_matrix_inv _ ?_).comp (hc.add continuousAt_const)
    obtain ⟨u, hu⟩ := hdet
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt

theorem betaH_apply (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]

theorem preimage_subset_image (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩

end SlopeTestRemainingChoices

end HcInf
