import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.MeanHeightDescent.BadRowsNumeric
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

theorem log_covolume_slope_mu : LcvMu := by
  intro K _ _ _ _ d hd X hX M hM
  have hfg : M.FG := Submodule.IsLattice.fg (self := hM)
  have hspan : Submodule.span K (M : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hM)
  have hrk : Formalism.HN.rkK M = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hne : M ≠ ⊥ := by
    intro h
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
      unfold Formalism.HN.rkK
      simp
    rw [h, h2] at hrk
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg).2.2
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, Formalism.DivisionValues.lcv, hn]
  field_simp

end Formalism.ExtensionFiltration
