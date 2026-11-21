import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExcRingPf
open LateralTheory.E.t_E6Cut

instance monoSch {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] : Mono (sch.map f) := by
  have h1 : ∀ n, Mono ((sch.map f).app n) := fun n => by
    have h2 : ∀ T, Mono (((sch.map f).app n).app T) := fun T => by
      rw [CategoryTheory.mono_iff_injective]
      intro u v h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

end LateralTheory.E.LeafExcRingPf
