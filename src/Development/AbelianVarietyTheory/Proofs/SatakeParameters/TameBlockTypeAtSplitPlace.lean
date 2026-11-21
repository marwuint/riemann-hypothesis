import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockPf

theorem splitAt : ∀ (D : D7) (w : PlE D.host), IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
  intro D w hw
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

end GlobalTheory.TypeBlockPf
