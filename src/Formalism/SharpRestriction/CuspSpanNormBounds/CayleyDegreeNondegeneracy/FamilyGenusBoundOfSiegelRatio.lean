import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  fun V _ _ _ _ h L _ hL M hlat hint huni x hx hx0 => exists_orthogonal_second_vector K hK V h L hL M hlat hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

end Formalism.MainNotions.BridgeLemma₂

end
