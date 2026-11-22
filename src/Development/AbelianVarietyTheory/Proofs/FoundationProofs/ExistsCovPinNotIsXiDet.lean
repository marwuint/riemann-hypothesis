import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RayContainment
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortSpanUnitOfExactValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverPinCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RayContainment
open GlobalTheory.ClsVal.Cmp (OverBase overBase_of_ne eq_incl coe_incl spMap_comp')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem nonempty_lift {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra K ℂ] [Module.Finite K L] :
    Nonempty (L →ₐ[K] ℂ) := ⟨IsAlgClosed.lift⟩

theorem exists_algHom_ker {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (m : Ideal p.R) [hm : m.IsMaximal] :
    ∃ ψ : p.R →ₐ[K] CAt σ, ∀ x, ψ x = 0 ↔ x ∈ m := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  obtain ⟨j⟩ := nonempty_lift (K := K) (L := p.R ⧸ m)
  refine ⟨(j.comp (Ideal.Quotient.mkₐ K m) : p.R →ₐ[K] ℂ), fun x => ?_⟩
  exact (map_eq_zero_iff j j.toRingHom.injective).trans Ideal.Quotient.eq_zero_iff_mem

theorem eq_of_complex (σ : c.F →+* ℂ) {f f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {w : ℕ} (hf : f ∈ sec Xo c a w)
    (hf' : f' ∈ sec Xo c a w) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c f y = evR Xo c f' y) : f = f' := by
  funext p y
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  haveI : IsJacobsonRing p.R := isJacobsonRing_of_finiteType (A := c.F)
  have hj : (⊥ : Ideal p.R).jacobson = ⊥ := IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker σ p m
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c _ _ ψ y
  rw [← hψ, map_sub, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf' ψ hz, h, sub_self]

end GlobalTheory.CoverPinCompare
