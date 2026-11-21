import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset

open IsDedekindDomain Function

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R]

theorem isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

end General

end GlobalTheory
