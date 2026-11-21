import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Sh

def NEFin (J : Type) : Type := {t : Finset J // t.Nonempty}

open Classical in

instance (J : Type) : SemilatticeInf (NEFin J) where
  le a b := b.1 ⊆ a.1
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ hab hbc := Finset.Subset.trans hbc hab
  le_antisymm a b hab hba := Subtype.ext (Finset.Subset.antisymm hba hab)
  inf a b := ⟨a.1 ∪ b.1, a.2.mono Finset.subset_union_left⟩
  inf_le_left _ _ := Finset.subset_union_left
  inf_le_right _ _ := Finset.subset_union_right
  le_inf _ _ _ hab hac := Finset.union_subset hab hac

instance (J : Type) [Finite J] : Finite (NEFin J) :=
  inferInstanceAs (Finite {t : Finset J // t.Nonempty})

end MainStatements.Hodge.Sh
