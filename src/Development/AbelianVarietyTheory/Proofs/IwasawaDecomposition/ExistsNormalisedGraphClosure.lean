import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

end GlobalTheory.GraphClosure
