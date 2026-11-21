import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def ren (π : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

theorem ren_apply (π : Equiv.Perm (Fin g)) (z : Fin g → ℂ) : ren π z = z ∘ π := rfl

theorem ren_single (π : Equiv.Perm (Fin g)) (j : Fin g) : ren π (Pi.single j 1) = Pi.single (π.symm j) 1 := by
  funext i
  rw [ren_apply, Function.comp_apply]
  by_cases h : i = π.symm j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    exact h (by rw [← h']; simp)

section Rename₂

variable (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (π : Equiv.Perm (Fin g))
  (x : Frame X.Ψ r)

theorem pv_ren (v : Fin r → E) : pv X (π.trans idx) x v = ren π (pv X idx x v) := rfl

private theorem perMat_trans_idx_eq_submatrix (s : Fin g → Fin g ⊕ Fin g) :
    perMat X bas (π.trans idx) s x = (perMat X bas idx s x).submatrix π (Equiv.refl _) := by
  ext i k
  simp [perMat_apply]

theorem hMat_ren : hMat X bas (π.trans idx) x = (hMat X bas idx x).submatrix (Equiv.refl _) π := by
  simp only [hMat]
  rw [perMat_trans_idx_eq_submatrix, Matrix.inv_submatrix_equiv]

theorem hMat_mulVec_ren (z : Fin g → ℂ) : hMat X bas (π.trans idx) x *ᵥ ren π z = hMat X bas idx x *ᵥ z := by
  rw [hMat_ren, ren_apply, Matrix.submatrix_mulVec_equiv]
  ext i
  simp [Function.comp_def]

theorem tauMat_ren : tauMat X bas (π.trans idx) x = tauMat X bas idx x := by
  simp only [tauMat]
  rw [hMat_ren, perMat_trans_idx_eq_submatrix, Matrix.submatrix_mul_equiv]
  simp

theorem imInv_ren : imInv X bas (π.trans idx) x = imInv X bas idx x := by
  simp only [imInv, tauMat_ren]

theorem hx_ren (z w : Fin g → ℂ) : hx X bas (π.trans idx) x (ren π z) (ren π w) = hx X bas idx x z w := by
  simp only [hx, hMat_mulVec_ren, imInv_ren]

variable {X bas idx x}

def anFibRen [Algebra c.F ℂ] {e : Fin g ≃ Lt1 Dw} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas (π.trans idx) (π.trans e) x L y) : AnFib X bas idx e x L y where
  ex z := A.ex (ren π z)
  ex_add z w := by rw [map_add, A.ex_add]
  ex_onto := A.ex_onto.comp (ren π).surjective
  ex_ker z := by simp only [A.ex_ker, pv_ren, (ren π).injective.eq_iff]
  ex_lin a z := A.ex_lin a (ren π z)
  hol U f := ⟨(A.hol U f).1.preimage (ren π).continuous,
    (A.hol U f).2.comp (ren π).differentiable.differentiableOn fun _ h => h⟩
  der ℓ := by
    refine ⟨by simpa only [map_zero] using (A.der ℓ).1, fun U h f => ((A.der ℓ).2 U h f).trans ?_⟩
    have := (ren π).comp_right_fderiv (f := fun z => valAt' (A.ex z).left U f) (x := 0)
    rw [map_zero] at this
    change _ = fderiv ℂ ((fun z => valAt' (A.ex z).left U f) ∘ ren π) 0 _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ren_single]
    rfl
  fr j z := A.fr j (ren π z)
  fr_hol j := (A.fr_hol j).comp (ren π).differentiable.differentiableOn fun _ h => h
  fr_ne j z := A.fr_ne j _
  fr_g j j' z := A.fr_g j j' _
  fr_0 j := by rw [map_zero]; exact A.fr_0 j
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z h := by
    rw [A.fr_per v hv j _ h, pv_ren, hx_ren, hx_ren, map_add]

end Rename₂

end

end GlobalTheory.ClsVal.Cmp
