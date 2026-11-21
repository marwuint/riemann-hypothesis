import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieNormSqIffEqPiDivCovolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CurveHomExtOfDerivativeLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory.CMPeriodCompare

section Analytic

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)}
    (he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ X} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e (L w) v) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => e (L z)) w v := by
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  refine ⟨by simpa using h0, fun U hU f => ?_⟩
  rw [h1 U hU f]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← h0]
    intro x _
    exact hU (by trivial)
  have hd := _root_.GlobalTheory.LocalLift.hol_differentiableAt he (Set.mem_univ 0) hU0 f
  unfold _root_.GlobalTheory.FibreDeriv.jet
  simp only [map_zero]
  congr 2
  have hd' : DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f)
      (LinearMap.toContinuousLinearMap L 0) := by
    simpa using hd
  have hc := hd'.hasFDerivAt.comp (0 : Fin g' → ℂ) (LinearMap.toContinuousLinearMap L).hasFDerivAt
  rw [show (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e (L z)) U f) =
      (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L) from rfl, hc.fderiv]
  simp

variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in
private theorem isDerivAt0_ex_of_isDiff_tangent (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g)
    {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (u.ex z).left) w t.left := by
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left = (u.ex 0).left := by
    rw [_root_.GlobalTheory.TangentOrigin.ex_zero_left]
    exact ht
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff]
  refine ⟨h0, fun U h f => ?_⟩
  ext
  · rw [_root_.GlobalTheory.FibreDeriv.fst_evEps _ _ h0, _root_.GlobalTheory.FibreDeriv.fst_jet]
  · have := hw U h f
    unfold _root_.GlobalTheory.FibreDeriv.jet
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [← this]
    rfl

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in

theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_line (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A}
    (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (g := 1) (fun z => (u.ex (z 0 • w)).left ≫ φ) (fun _ => 1) (t.left ≫ φ) := by
  have hu := isDerivAt0_ex_of_isDiff_tangent u ht hw
  have he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => (u.ex z).left) := by
    simpa using _root_.GlobalTheory.HomLinear.isHolTo_ex_comp u (𝟙 _)
  let L : (Fin 1 → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) := (LinearMap.proj 0).smulRight w
  have hL : L (fun _ => 1) = w := by simp [L]
  rw [← hL] at hu
  exact _root_.GlobalTheory.FibreDeriv.isDerivAt0_comp (_root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear he L hu) φ

variable {v : epsR R ⟶ P.A}

variable {ex : ℂ → (Over.mk (spMap s) ⟶ P.A)} {Λ : Submodule ℤ ℂ}

end Analytic

end GlobalTheory.CMPeriodCompare
