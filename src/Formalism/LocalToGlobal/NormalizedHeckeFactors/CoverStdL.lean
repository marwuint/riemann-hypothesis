import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverFP
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam

end Formalism.L2
