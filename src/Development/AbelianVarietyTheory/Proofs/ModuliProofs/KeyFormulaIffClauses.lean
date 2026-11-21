import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialDifferential
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PolarizationCorrespondence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsBaseChangeIffKeyPB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence GlobalTheory.KeyInputCompare

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

namespace Same

end Same

end Unif

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
