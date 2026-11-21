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

theorem mat_split_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {Y Z : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (h1 : Y.map (splitProj t) = Z.map (splitProj t))
    (h2 : Y.map (splitProj (t.comp σ)) = Z.map (splitProj (t.comp σ))) : Y = Z := by
  ext i j
  exact split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

theorem pairMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B A' B' : Matrix (Fin n) (Fin n) (Fv F v)) :
    pairMat h t A B * pairMat h t A' B' = pairMat h t (A * A') (B * B') :=
  mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst])
    (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])

theorem pairMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    pairMat h t (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 = 1 :=
  mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])

def conjComp (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v) :=
  (J.map t)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map t

theorem conjComp_mul (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map t).det)
    (g₁ g₂ : GL (Fin n) (Fv F v)) : conjComp t J (g₁ * g₂) = conjComp t J g₁ * conjComp t J g₂ := by
  simp only [conjComp, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem conjComp_one (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map t).det) :
    conjComp t J 1 = 1 := by
  simp only [conjComp, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hJ

def locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := pairMat h t g (conjComp t J g)

theorem locMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (g₁ g₂ : GL (Fin n) (Fv F v)) :
    locMat h t J (g₁ * g₂) = locMat h t J g₁ * locMat h t J g₂ := by
  rw [locMat, locMat, locMat, pairMat_mul, conjComp_mul t J hJ, Units.val_mul]

theorem locMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) : locMat h t J 1 = 1 := by
  rw [locMat, conjComp_one t J hJ, Units.val_one, pairMat_one]

theorem locMat_unitary (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (herm : ∀ i j, σ (J j i) = J i j) (g : GL (Fin n) (Fv F v)) :
    (locMat h t J g)ᵀ * J.map (inclR (Fv F v)) * (locMat h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, locMat, pairMat_snd]
  have hs2 : ((locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = (J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply]
    rw [← herm j i]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one, Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v)) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end Local

section Hom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def adelicGL (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (g : GL (Fin n) (Fv F v)) : GL (Fin n) (AE F E) :=
  ⟨lift v (locMat h t J g), lift v (locMat h t J g⁻¹),
    by rw [lift_mul, ← locMat_mul h t J hJ, mul_inv_cancel, locMat_one h t J hJ, lift_one],
    by rw [lift_mul, ← locMat_mul h t J hJ, inv_mul_cancel, locMat_one h t J hJ, lift_one]⟩

def leviHom (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (herm : ∀ i j, σ (J j i) = J i j) : GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨adelicGL h t J hJ g, lift_unitary v σ J _ (locMat_unitary h t J hJ herm g)⟩
  map_one' := Subtype.ext (Units.ext (by
    change lift v (locMat h t J 1) = 1
    rw [locMat_one h t J hJ, lift_one]))
  map_mul' g₁ g₂ := Subtype.ext (Units.ext (by
    change lift v (locMat h t J (g₁ * g₂)) = lift v (locMat h t J g₁) * lift v (locMat h t J g₂)
    rw [locMat_mul h t J hJ, lift_mul]))

theorem mat_leviHom (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (herm : ∀ i j, σ (J j i) = J i j) (g : GL (Fin n) (Fv F v)) :
    mat (leviHom h t J hJ herm g) = lift v (locMat h t J g) := rfl

end Hom

end GlobalTheory.LeviAtPlace
