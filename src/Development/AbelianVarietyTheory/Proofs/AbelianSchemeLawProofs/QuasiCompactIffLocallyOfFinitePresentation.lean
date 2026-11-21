import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.SemiAbelianCompare

section General

theorem geometricallyConnected_of_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      ConnectedSpace ↥(pullback f s)) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let b : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hb : Surjective b := ⟨fun z => ⟨_, Subsingleton.elim (b (default : PrimeSpectrum _)) z⟩⟩
  have := h _ (b ≫ y)
  let g := (pullbackLeftPullbackSndIso f y b).inv ≫ pullback.fst (pullback.snd f y) b
  exact g.surjective.connectedSpace g.continuous

end General

end GlobalTheory.SemiAbelianCompare

namespace GlobalTheory

end GlobalTheory
