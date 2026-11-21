import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section Fibres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))

def specialι : specialFibre f ⟶ Z := pullback.fst _ _

end Fibres

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
