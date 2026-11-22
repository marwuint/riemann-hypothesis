import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points

namespace GlobalTheory.AmpleModelPos

theorem isGenerated_tens {X : Scheme.{0}} {A B : LB X} (hA : IsGenerated A) (hB : IsGenerated B) :
    IsGenerated (tens A B) := by
  obtain ⟨a, s, hs⟩ := hA
  obtain ⟨b, t, ht⟩ := hB
  refine isGenerated_of_finite (fun q : Fin a × Fin b => EndOnTorsion.tensSec (s q.1) (t q.2))
    (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (EndOnTorsion.nonzeroLocus_tensSec (s i) (t j)).ge ⟨hi, hj⟩⟩

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end GlobalTheory.AmpleModelPos
