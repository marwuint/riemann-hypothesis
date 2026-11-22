import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.BlockTheory.EvidentLattices.LatticeLetterSources
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
