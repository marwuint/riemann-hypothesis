import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DiscriminantKernelAutomorphisms

noncomputable section

open scoped Classical

namespace GlobalTheory.RowMassCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gmap

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mul' (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

end Gmap

section Stab

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem mul_mem_stabF {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) :
    a * b ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [this, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · show a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Stab

end GlobalTheory.RowMassCompare

end
