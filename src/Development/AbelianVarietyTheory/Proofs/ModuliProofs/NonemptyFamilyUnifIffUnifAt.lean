import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty

noncomputable section

namespace GlobalTheory.UnifCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel GlobalTheory.PeriodCompare
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem isPeriod_move {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ P₁ P : D'.La →+ (Fin g → ℂ)}
    (h₀ : IsPeriod D' ty P₀) (h₁ : IsPeriod D' ty P₁) (hP : IsPeriod D' ty P) (gam : D'.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hgam : ∀ a b, D'.EF (gam a) (gam b) = D'.EF a b)
    (hh : ∀ a, P₁ (gam a) = h (P₀ a)) :
    IsPeriod D' ty (h.toLinearMap.toAddMonoidHom.comp (P.comp gam.symm.toLinearMap.toAddMonoidHom)) := by
  have tr : ∀ {Q : D'.La →+ (Fin g → ℂ)}, IsPeriod D' ty Q →
      IsPeriod D' ty (Q.comp gam.symm.toLinearMap.toAddMonoidHom) := by
    rintro Q ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩
    have hr : (Q.comp gam.symm.toLinearMap.toAddMonoidHom).range = Q.range :=
      SetLike.ext' (gam.symm.surjective.range_comp Q)
    refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
    · simpa using h1 a (gam.symm x) i
    · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    · change (hermForm Hm (Q (gam.symm x)) (Q (gam.symm y))).im = _
      rw [h7, ← hgam, gam.apply_symm_apply, gam.apply_symm_apply]
  let A := LinearMap.toMatrix' h.toLinearMap
  have hA : A.mulVecLin = h.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact h.isUnit_det'.ne_zero
  rw [← hA]
  refine PeriodConn.isPeriod_mulVec (tr hP) hdet (PeriodConn.entry_eq_zero (tr h₀) h₁ fun x => ?_)
  rw [← Matrix.mulVecLin_apply, hA]
  exact (congrArg P₁ (gam.apply_symm_apply x)).symm.trans (hh _)

variable {g : ℕ}

variable {D' : Datum H} {ty : Fin g → (E →+* ℂ)}

end Lattice

section Deriv

variable {X S : Scheme.{0}} {g : ℕ}

theorem isDerivAt0_smul {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : IsDerivAt0 F w v) (c : ℂ) : IsDerivAt0 F (c • w) (spMap (epsScale c) ≫ v) := by
  have h0 : spMap TangentOrigin.fstC ≫ spMap (epsScale c) ≫ v = spMap TangentOrigin.fstC ≫ v := by
    rw [← Category.assoc, TanMod.spMap_comp']
    congr 2
    exact RingHom.ext fun x => by simp [epsScale]
  refine ⟨h0.trans hv.1, fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff] at h ⊢
    exact h0 ▸ h
  refine (congrArg TrivSqZeroExt.snd (TangentOrigin.evalPt_spMap_comp (epsScale c) v U h' h f)).trans ?_
  rw [map_smul, ← hv.2 U h' f]
  exact TrivSqZeroExt.snd_map _ _

theorem isDerivAt0_mul {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {F : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    (h0 : F 0 = (1 : Over.mk y ⟶ G).left) {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt0 F w v.left) (hv' : IsDerivAt0 F w' v'.left) : IsDerivAt0 F (w + w') (v * v').left := by
  have t := TanMod.smT_zero_of y v (hv.1.trans h0)
  have t' := TanMod.smT_zero_of y v' (hv'.1.trans h0)
  have t'' : spMap TangentOrigin.fstC ≫ (v * v').left = F 0 :=
    (TanMod.unit_of_smT_zero y (v * v') (by rw [TanMod.smT_mul, t, t', _root_.mul_one])).trans h0.symm
  refine ⟨t'', fun U h f => ?_⟩
  have hF : ⊤ ≤ F 0 ⁻¹ᵁ U := t'' ▸ (TangentOrigin.top_le_preimage_iff _ U).1 h
  have h1 := (TangentOrigin.top_le_preimage_iff v.left U).2 (hv.1.symm ▸ hF)
  have h2 := (TangentOrigin.top_le_preimage_iff v'.left U).2 (hv'.1.symm ▸ hF)
  rw [map_add, ← hv.2 U h1 f, ← hv'.2 U h2 f]
  exact TanDeriv.snd_evAt_mul v v' t t' U h1 h2 h f

end Deriv

end GlobalTheory.UnifCompare
