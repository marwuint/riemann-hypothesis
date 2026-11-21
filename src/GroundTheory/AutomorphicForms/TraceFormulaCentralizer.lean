import Mathlib
import GroundTheory.AutomorphicForms.TraceFormulaGeometric

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Maps

variable {G : Type*} [Group G]

def mapOfLe {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : RightCosetSpace H₁ → RightCosetSpace H₂ :=
  Quotient.map' id (by
    rintro a b ⟨η, rfl⟩
    exact ⟨⟨η, h η.2⟩, rfl⟩)

@[simp] theorem mapOfLe_mk {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (x : G) :
    mapOfLe h (mk H₁ x) = mk H₂ x :=
  rfl

def centralizerLattice (Γ : Subgroup G) (γ : G) : Subgroup (Subgroup.centralizer {γ}) :=
  Γ.comap (Subgroup.centralizer {γ}).subtype

theorem mem_centralizerLattice {Γ : Subgroup G} {γ : G} {h : Subgroup.centralizer {γ}} :
    h ∈ centralizerLattice Γ γ ↔ (h : G) ∈ Γ :=
  Iff.rfl

end Maps

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem isClosed_centralizer (γ : G) : IsClosed (Subgroup.centralizer {γ} : Set G) :=
  Set.isClosed_centralizer {γ}

instance locallyCompactSpace_centralizer [LocallyCompactSpace G] (γ : G) :
    LocallyCompactSpace (Subgroup.centralizer {γ}) :=
  (isClosed_centralizer γ).locallyCompactSpace

instance discreteTopology_centralizerLattice (Γ : Subgroup G) [DiscreteTopology Γ] (γ : G) :
    DiscreteTopology (centralizerLattice Γ γ) :=
  DiscreteTopology.of_continuous_injective
    (f := fun h : centralizerLattice Γ γ => (⟨((h : Subgroup.centralizer {γ}) : G), h.2⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b hab => by
      simp only at hab
      exact Subtype.ext (Subtype.ext (by injection hab)))

instance secondCountableTopology_centralizer [SecondCountableTopology G] (γ : G) :
    SecondCountableTopology (Subgroup.centralizer {γ}) :=
  inferInstanceAs (SecondCountableTopology (Subgroup.centralizer {γ} : Set G))

variable [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

end Topology

end RightCosetSpace

end

end GroundTheory.Automorphic
