import Mathlib

import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open Matrix TensorProduct GroundTheory.Automorphic Topology

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [local instance] scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem t2Space_tensor_product [T2Space R] : T2Space (R ⊗[K] E) := t2Space_tensor R

theorem locallyCompactSpace_A [LocallyCompactSpace R] : LocallyCompactSpace (R ⊗[K] E) :=
  (tensorCoordsHomeomorph R (Module.finBasis K E)).isClosedEmbedding.locallyCompactSpace

theorem secondCountableTopology_A [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[K] E) :=
  (tensorCoordsHomeomorph R (Module.finBasis K E)).isEmbedding.secondCountableTopology

section Spaces

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

instance instIsTopologicalAddGroupFrameSp : IsTopologicalAddGroup (FrameSp K E R ι p) :=
  inferInstanceAs (IsTopologicalAddGroup (ι → Fin p → R ⊗[K] E))

instance instLocallyCompactSpaceFrameSp : LocallyCompactSpace (FrameSp K E R ι p) := by
  have := locallyCompactSpace_A (K := K) (E := E) (R := R)
  exact inferInstanceAs (LocallyCompactSpace (ι → Fin p → R ⊗[K] E))

instance instT2SpaceFrameSp : T2Space (FrameSp K E R ι p) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact inferInstanceAs (T2Space (ι → Fin p → R ⊗[K] E))

instance instSecondCountableTopologyFrameSp : SecondCountableTopology (FrameSp K E R ι p) := by
  have := secondCountableTopology_A (K := K) (E := E) (R := R)
  exact inferInstanceAs (SecondCountableTopology (ι → Fin p → R ⊗[K] E))

theorem isClosed_hermSub :
    IsClosed (hermSub K E R p : Set (Matrix (Fin p) (Fin p) (R ⊗[K] E))) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact isClosed_eq ((continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose)
    continuous_id

instance instIsTopologicalAddGroupHermSp : IsTopologicalAddGroup (HermSp K E R p) :=
  inferInstanceAs (IsTopologicalAddGroup (hermSub K E R p))

instance instLocallyCompactSpaceHermSp : LocallyCompactSpace (HermSp K E R p) := by
  have := locallyCompactSpace_A (K := K) (E := E) (R := R)
  exact (isClosed_hermSub (K := K) (E := E) (R := R) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instT2SpaceHermSp : T2Space (HermSp K E R p) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact inferInstanceAs (T2Space (hermSub K E R p))

instance instSecondCountableTopologyHermSp : SecondCountableTopology (HermSp K E R p) := by
  have := secondCountableTopology_A (K := K) (E := E) (R := R)
  have : SecondCountableTopology (Matrix (Fin p) (Fin p) (R ⊗[K] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin p → Fin p → R ⊗[K] E))
  exact (Topology.IsEmbedding.subtypeVal (p := fun S ↦ S ∈ hermSub K E R p)).secondCountableTopology

end Spaces

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
