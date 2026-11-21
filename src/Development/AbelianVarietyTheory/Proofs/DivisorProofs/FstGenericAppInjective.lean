import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

end GlobalTheory.Mum
