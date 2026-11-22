import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.NGLeaves

open Formalism.BasicNotions Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

theorem nondegenerate_gram_tuple : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 = PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

end Formalism.L2.SG.NGLeaves
