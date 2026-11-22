import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePair

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem away_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact _root_.GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair S hD ⟨J.alg0, J.alg⟩ J.kin (_root_.GlobalTheory.TwV.pos_at_site S) (_root_.GlobalTheory.pairOK_allSites S hD)

end GlobalTheory.TwV
