import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsType

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (h : GAf L n)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S) : NG.rt L n h f ∈ NG.isoTyp ρ S := by
  have hle : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    have hU' : U ≤ NG.isoTyp ρ S := le_sSup hU
    exact hU' (hU.1.1.stable h a ha)
  exact hle hf

end GlobalTheory.CenKeepsType
