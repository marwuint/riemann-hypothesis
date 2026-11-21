import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.Pst

namespace UpperTheory.Lit.Drps

variable {l : ℕ} [Fact l.Prime]

section Coord

variable {S : Type} [CommRing S] [Algebra ℚ_[l] S] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {d : ℕ} (b : Basis (Fin d) ℚ_[l] V)

def cS (i : Fin d) : V ⊗[ℚ_[l]] S →ₗ[ℚ_[l]] S :=
  (TensorProduct.lid ℚ_[l] S).toLinearMap ∘ₗ (b.coord i).rTensor S

@[simp] theorem cS_tmul (i : Fin d) (v : V) (s : S) : cS b i (v ⊗ₜ s) = b.coord i v • s := by
  simp [cS]

end Coord

end UpperTheory.Lit.Drps
