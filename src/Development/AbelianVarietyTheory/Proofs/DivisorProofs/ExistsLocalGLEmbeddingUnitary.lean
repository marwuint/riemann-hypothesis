import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LeviAtPlace

open GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def ext0 (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (AE F E) := M.map (tensAt E v)

theorem matrixExtendByZero_add (M N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : ext0 v (M + N) = ext0 v M + ext0 v N := by
  ext i j; simp [ext0]

theorem matrixExtendByZero_zero : ext0 v (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 0 := by
  ext i j; simp [ext0]

theorem ext_zero_mul_right (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (C : Matrix (Fin n) (Fin n) (AE F E)) :
    ext0 v M * C = ext0 v (M * C.map (compFin F E v)) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]

theorem ext_zero_mul_left (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (C : Matrix (Fin n) (Fin n) (AE F E)) :
    C * ext0 v M = ext0 v (C.map (compFin F E v) * M) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, tensAt_mul_right, mul_comm]

theorem matrixExtendByZero_mul (M N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : ext0 v M * ext0 v N = ext0 v (M * N) := by
  rw [ext_zero_mul_right]
  congr 2
  ext i j
  exact compFin_tensAt v _

theorem ext_zero_transpose (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

theorem ext_zero_map_conj (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    (ext0 v M).map (cA σ) = ext0 v (M.map (sigR (Fv F v) σ)) := by
  ext i j
  exact sigR_tensAt v σ _

def lift (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (AE F E) := 1 + ext0 v (Y - 1)

theorem lift_mul (Y Z : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : lift v Y * lift v Z = lift v (Y * Z) := by
  have e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by noncomm_ring
  rw [lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]
  noncomm_ring

theorem lift_one : lift v (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
  rw [lift, sub_self, matrixExtendByZero_zero, add_zero]

theorem lift_unitary (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hY : Yᵀ * J.map (inclR (Fv F v)) * Y.map (sigR (Fv F v) σ) = J.map (inclR (Fv F v))) :
    (lift v Y)ᵀ * incM F J * (lift v Y).map (cA σ) = incM F J := by
  set C := incM F J
  have hC : C.map (compFin F E v) = J.map (inclR (Fv F v)) := by
    ext i j
    change compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j
    change evFin F v 1 ⊗ₜ[F] J i j = _
    rw [map_one]
  have hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ := by
    rw [lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]
  have hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ)) := by
    rw [← ext_zero_map_conj]
    ext i j
    simp [lift, Matrix.one_apply]
  rw [hT, hS]
  have e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) =
      C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) +
        ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ))) := by noncomm_ring
  rw [e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]
  have hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1 := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hYs, Matrix.transpose_sub, Matrix.transpose_one]
  set Jl : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))
  have e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) =
      Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl := by noncomm_ring
  rw [e2, hY, sub_self, matrixExtendByZero_zero, add_zero]

end Lift

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem map_mul_alg (f : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (M N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

def conjComp (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v) :=
  (J.map t)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map t

def locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := pairMat h t g (conjComp t J g)

end Local

section Hom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

end Hom

end GlobalTheory.LeviAtPlace
