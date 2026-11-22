import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerLeviDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev gm {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : Matrix (Fin n) (Fin n) (AE F E) := (matHom _ σ J p).1

theorem gm_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : gm (1 : GAd σ J) = 1 := by
  simp only [gm, map_one, Units.val_one]

theorem gm_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p q : GAd σ J) : gm (p * q) = gm p * gm q := by
  simp only [gm, map_mul, Units.val_mul]

theorem gm_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : gm p⁻¹ * gm p = 1 := by
  simp only [gm, map_inv]; exact Units.inv_mul _

theorem fR_gm (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (p : GAd σ (c • J.map σ)) (u v : Fin n → AE F E) :
    fR (cA σ).toRingHom (incM F J) (gm p *ᵥ u) (gm p *ᵥ v) = fR (cA σ).toRingHom (incM F J) u v := by
  have hU : (gm p)ᵀ * incM F J * (gm p).map (cA σ).toRingHom = incM F J :=
    ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ J hc).symm p).2
  rw [fR_mulVec, hU]; rfl

theorem mul_fR_eq_one (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0)
    {x y : Fin n → E} (hxy : form σ J x y = 1) (p : GAd σ (c • J.map σ)) {t : AE F E}
    (ht : gm p *ᵥ incV F x = t • incV F x) : t * fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = 1 := by
  have h := fR_gm hσ J hc p (incV F x) (incV F y)
  rw [ht, fR_smul_left, fR_inc, hxy, map_one] at h
  exact h

def stab (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (x y : Fin n → E) (hxy : form σ J x y = 1) : Subgroup (GAd σ (c • J.map σ)) where
  carrier := {p | ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x}
  one_mem' := ⟨1, by rw [gm_one, Matrix.one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro p q ⟨t, ht⟩ ⟨s, hs⟩
    refine ⟨s * t, ?_⟩
    rw [gm_mul, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul, ht, smul_smul]
  inv_mem' := by
    rintro p ⟨t, ht⟩
    refine ⟨fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y), ?_⟩
    have e := mul_fR_eq_one hσ hc hxy p ht
    have h1 : incV F x = t • (gm p⁻¹ *ᵥ incV F x) := by
      rw [← Matrix.mulVec_smul, ← ht, Matrix.mulVec_mulVec, gm_inv_mul, Matrix.one_mulVec]
    generalize fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = s at e ⊢
    calc gm p⁻¹ *ᵥ incV F x = (t * s) • (gm p⁻¹ *ᵥ incV F x) := by rw [e, one_smul]
      _ = s • (t • (gm p⁻¹ *ᵥ incV F x)) := by rw [smul_smul, mul_comm]
      _ = s • incV F x := by rw [← h1]

theorem mem_stab {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1} {p : GAd σ (c • J.map σ)} :
    p ∈ stab hσ J hc x y hxy ↔ ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x := Iff.rfl

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

variable {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1}

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE' : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

variable (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) {c : E} (hc : c ≠ 0)
  (hxy : form σ W.J H.x H.y = 1)

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

end GlobalTheory.StabLine
