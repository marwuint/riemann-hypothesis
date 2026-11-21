import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowUnitProof

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x, hx, hy⟩ := hw
  have hc : IsSplitPl D.host (GlobalTheory.SplitConjPlace.conjPlE w) := by
    refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E x, ?_, fun y hy' => ?_⟩
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]; exact hx
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
      apply hy
      rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, hy', hstar, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hc
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have h1 := hs (IsCMField.ringOfIntegersComplexConj D.host.E y) y (by
    rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply])
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO] at h1
  exact h1.symm

end GlobalTheory.RowUnitProof

namespace GlobalTheory.RowUnitProof

end GlobalTheory.RowUnitProof

end
