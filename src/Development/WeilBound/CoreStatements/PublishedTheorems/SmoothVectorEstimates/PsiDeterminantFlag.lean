import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

open GlobalTheory.CuspRep

namespace PositivityTheory.jumpWindows

theorem mean_convergence_of : Smo → GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  refine congrArg CuspSub.V (h E a π π' ?_)
  filter_upwards [_root_.GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩

end PositivityTheory.jumpWindows
