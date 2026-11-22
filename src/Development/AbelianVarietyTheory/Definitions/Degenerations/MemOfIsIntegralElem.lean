import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionTwistTsumNormGe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ToricData GlobalTheory.HostModel GlobalTheory.HostModel.ConjDual GlobalTheory.Ex.ValInh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex

section Valued

theorem mem_of_isIntegralElem {R C : Type} [CommRing R] [Field C] (S : ValuationSubring C) (j : R →+* C) (hj : ∀ r, j r ∈ S)
    {x : C} (hx : j.IsIntegralElem x) : x ∈ S := by
  obtain ⟨p, hp, h⟩ := hx
  have : IsIntegral S x := ⟨p.map (j.codRestrict S.toSubring hj), hp.map _, by rw [Polynomial.eval₂_map]; exact h⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

variable {O' : Type} [CommRing O'] [IsDomain O'] {R₁ : Type} [CommRing R₁] (g : PowerSeries O' →+* R₁) {K : Type} [Field K]
  (i : R₁ →+* K)

theorem not_allC_false (hi : Function.Injective (i.comp g))
    (halg : ∀ x : K, ∃ p : Polynomial (PowerSeries O'), p ≠ 0 ∧ p.eval₂ (i.comp g) x = 0) (hg : g.IsIntegral) :
    ¬ AllC g i fun _ _ => False := by
  intro h
  let V := PowerSeries (FractionRing O')
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V (FractionRing V)
    (a := PowerSeries.X) PowerSeries.X_ne_zero (fun e => not_isUnit_zero (PowerSeries.constantCoeff_X (R := FractionRing O') ▸ e.map PowerSeries.constantCoeff))
    (r := 1 / 2) (by norm_num) (by norm_num)
  let j₀ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  let j : PowerSeries O' →+* C := j₀.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hj : Function.Injective j := ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _)).comp
    (PowerSeries.map_injective _ (IsFractionRing.injective O' _))
  letI : Algebra (PowerSeries O') K := (i.comp g).toAlgebra
  letI : Algebra (PowerSeries O') C := j.toAlgebra
  haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  haveI : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  haveI : Algebra.IsAlgebraic (PowerSeries O') K := ⟨halg⟩
  let gam : K →ₐ[PowerSeries O'] C := IsAlgClosed.lift
  have hc : ∀ f, gam.toRingHom (i (g f)) = j f := fun f => gam.commutes f
  letI : Algebra (FractionRing O') C := (j₀.comp PowerSeries.C).toAlgebra
  have hX : j PowerSeries.X = j₀ PowerSeries.X := congrArg j₀ (PowerSeries.map_X _)
  refine h C gam.toRingHom (Units.mk0 (j PowerSeries.X) fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm)))
    (fun x => (congrArg j₀ (PowerSeries.map_C _ x).symm).trans (hc _).symm) (fun r => ?_) (hc _).symm ?_
  · refine mem_normIntegers_iff.1 (mem_of_isIntegralElem _ j (fun f => mem_normIntegers_iff.2 ((h1 _).2 ⟨_, rfl⟩)) ?_)
    obtain ⟨p, hp, e⟩ := hg r
    refine ⟨p, hp, ?_⟩
    have := congrArg (gam.toRingHom.comp i) e
    rwa [map_zero, Polynomial.hom_eval₂, show (gam.toRingHom.comp i).comp g = j from RingHom.ext hc] at this
  · rw [Units.val_mk0, hX]
    exact h2.trans_lt (by norm_num)

theorem SerBase.not_allC_false {K : Type} [Field K] [Algebra (FractionRing O') K] {i : PowerSeries O' →+* K} (hi : SerBase i) :
    ¬ AllC (RingHom.id _) i fun _ _ => False :=
  GlobalTheory.Ex.not_allC_false (RingHom.id _) i hi.inj hi.alg (RingHom.isIntegral_of_surjective _ Function.surjective_id)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {b : O →+* O'} {Y : Model Xo c β} [IsDomain R₁] {g}
  {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}

end Valued

namespace StepInh
section Settings
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cExt (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (h : CDV W) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C)
      (_ : CharZero C) (_ : Algebra (FractionRing W) C), CExt W (IsLocalRing.maximalIdeal W) C := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W)
    hp.ne_zero (hp.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p) (r := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, _, ‹_›, ‹_›, ‹_›, charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective, _,
    fun r => (h1 _).2 ⟨r, rfl⟩, fun r hr => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 (hp.maximalIdeal_eq ▸ hr)
  have := (h1 _).2 ⟨s, rfl⟩
  rw [map_mul, map_mul, norm_mul, h2]
  linarith

end Settings

end StepInh
end GlobalTheory.Ex
end
