import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

abbrev MultiRing (K : Type) [Field K] (r : ℕ) : Type :=
  Localization.Away (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)

namespace MultiRing

variable {K : Type} [Field K] {r : ℕ}

theorem prod_X_ne_zero : (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ h => by simpa using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h

theorem powers_le : Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K) ≤ nonZeroDivisors _ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors prod_X_ne_zero

instance instIsDomain : IsDomain (MultiRing K r) :=
  haveI := GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r
  IsLocalization.isDomain_localization powers_le

instance instIsIntegrallyClosed : IsIntegrallyClosed (MultiRing K r) :=
  haveI := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries K r
  haveI := GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r
  isIntegrallyClosed_of_isLocalization (MultiRing K r)
    (Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)) powers_le

instance instIsNoetherianRing : IsNoetherianRing (MultiRing K r) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)) _ inferInstance

def u (i : Fin r) : MultiRing K r := algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r) (MvPowerSeries.X i)

section Spec

variable (a : Fin r → ℕ) (ha : ∀ i, 1 ≤ a i)
include ha

theorem hasSubst : MvPowerSeries.HasSubst fun i => (PowerSeries.X ^ a i : PowerSeries K) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    change PowerSeries.constantCoeff (PowerSeries.X ^ a i : PowerSeries K) = 0
    simp [show a i ≠ 0 from Nat.one_le_iff_ne_zero.1 (ha i)]

def specPS : MvPowerSeries (Fin r) K →+* PowerSeries K :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst a ha)).toRingHom

@[simp] theorem specPS_X (i : Fin r) : specPS a ha (MvPowerSeries.X i) = (PowerSeries.X ^ a i : PowerSeries K) :=
  MvPowerSeries.substAlgHom_X _ i

@[simp] theorem specPS_C (c : K) : specPS a ha (MvPowerSeries.C c) = PowerSeries.C c :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst a ha)).commutes c

def spec : MultiRing K r →+* LaurentSeries K :=
  IsLocalization.Away.lift (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)
    (g := (HahnSeries.ofPowerSeries ℤ K).comp (specPS a ha)) (IsUnit.mk0 _ (by
      rw [RingHom.comp_apply, map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using fun h => absurd h PowerSeries.X_ne_zero))

@[simp] theorem spec_algebraMap (f : MvPowerSeries (Fin r) K) :
    spec a ha (algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r) f) = HahnSeries.ofPowerSeries ℤ K (specPS a ha f) :=
  IsLocalization.Away.lift_eq _ _ f

@[simp] theorem spec_u (i : Fin r) : spec a ha (u i : MultiRing K r) = HahnSeries.single (a i : ℤ) 1 := by
  rw [u, spec_algebraMap, specPS_X, HahnSeries.ofPowerSeries_X_pow]

end Spec

end MultiRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F) {r : ℕ}

namespace IsMultiArc

end IsMultiArc

end GlobalTheory.LocM.FJ
