import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NL

theorem usedLocalConclusion_and_prvE : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, hE⟩ := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  refine ⟨⟨fun l _ K s LL g => ⟨p1 l K s LL g, p2 l K s LL g, p3 l K s LL g, p4 l K s LL g, p5 l K s LL g,
    p6 l K s LL g, p7 l K s LL g, p8 l K s LL g, p9 l K s LL g, p10 l K s LL g⟩, c2,
    (DeltaInvariantLattices.herr_prop_two_iff D HW F).2 ⟨a, b, c, d⟩, l3⟩, hE⟩

end GlobalTheory.NL
