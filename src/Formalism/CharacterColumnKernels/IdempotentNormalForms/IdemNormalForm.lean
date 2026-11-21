import Formalism.CharacterColumnKernels.StatOntoLattice

open Module

noncomputable section

namespace Formalism.NG

theorem burnside : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm

end Formalism.NG
