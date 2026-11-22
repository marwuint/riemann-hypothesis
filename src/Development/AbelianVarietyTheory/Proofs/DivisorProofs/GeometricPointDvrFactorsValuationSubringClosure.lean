import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geomPoint_factors_valuationSubring_algClosure :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
      [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W),
      ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k),
        (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧
          x = spMap h ≫ spMap j := by
  intro W L _ _ _ _ _ _ k _ _ x
  set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'
  have hinj : Function.Injective j' :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)
  set g : W →+* k := (Spec.preimage x).hom with hg
  obtain ⟨U, hU, h, hh⟩ := _root_.GlobalTheory.ValExt.exists_valuationSubring_ext W (AlgebraicClosure L) k j' hinj g
  refine ⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩
  · ext w; rfl
  · have hcomp : h.comp (j'.codRestrict U.toSubring hU) = g := by
      ext w; exact hh w
    have hx : x = Spec.map (Spec.preimage x) := (Spec.map_preimage x).symm
    rw [hx]
    simp only [spMap, Sp]
    rw [← Spec.map_comp]
    congr 1
    ext w
    change g w = h (j'.codRestrict U.toSubring hU w)
    rw [← hcomp]; rfl

end GlobalTheory
