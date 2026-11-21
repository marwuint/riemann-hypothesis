import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.ProfiniteCohomology.BridgeDefs
import GroundTheory.ProfiniteCohomology.BridgeNested
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => Fin.partialProd g := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

variable {k : Type u} [CommRing k]

theorem isLocallyConstant_ρ_apply {Y : Type*} [TopologicalSpace Y] (A : Rep.{u} k G)
    [IsDiscreteRep A] {p : Y → G} (hp : Continuous p) {ψ : Y → A} (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun y => A.ρ (p y) (ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h1 : ∀ᶠ z in nhds y, ψ z = ψ y := hψ.eventually_eq y
  have h2 : ∀ᶠ z in nhds y, A.ρ (p z) (ψ y) = A.ρ (p y) (ψ y) :=
    hp.continuousAt.eventually ((isLocallyConstant_apply A (ψ y)).eventually_eq (p y))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]

end General

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsDiscreteRep (underlyingRep X)]

def toInhomogeneous (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    locallyConstantCochains (underlyingRep X) n :=
  ⟨fun g => nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g),
    (IsLocallyConstant.iff_continuous _).2
      ((nestedHomeomorph X (n + 1) σ.1).continuous.comp (continuous_partialProd n))⟩

omit [IsDiscreteRep (underlyingRep X)] in
theorem toInhomogeneous_apply (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) (g : Fin n → G) :
    (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g =
      nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g) :=
  rfl

end GroundTheory.ProfCoh
