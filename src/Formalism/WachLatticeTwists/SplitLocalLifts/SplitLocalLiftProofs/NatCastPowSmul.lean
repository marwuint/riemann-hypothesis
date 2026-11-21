import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

theorem mono : StatMono := by
  intro O _ ℓ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e e' hee h κ hκ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hee
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (h κ hκ)

end Formalism.RepresentationBoundsCohomology.JL
