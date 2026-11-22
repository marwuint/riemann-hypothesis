import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := _root_.GlobalTheory.SkewDetParity.det_eq_unit_mul_norm F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj F E σ B hT.base v w hvw hF u hu
  refine _root_.GlobalTheory.SkewLagr.exists_isLagr_tensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (_root_.GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
