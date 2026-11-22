import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitUnitLift

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl F} {n : ℕ}

theorem unitary_eps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * incM F J *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (cA σ) = incM F J := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 :=
    Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F := F) (AF F))) = J.map τ :=
      Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ *
      ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F := F) (AF F))) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ *
      (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

def liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* Matrix (Fin n) (Fin n) (AE F E) :=
  (oneAdd (liftMat h τ)).comp (pairHom (J.map τ) hJ)

def liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨⟨liftN h τ J hJ g, liftN h τ J hJ g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
    by rw [← map_mul, inv_mul_cancel, map_one]⟩, unitary_eps h τ J ε herm hJ g⟩
  map_one' := Subtype.ext (Units.ext (map_one (liftN h τ J hJ)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (liftN h τ J hJ) g g'))

end GlobalTheory.SplitUnitLift
