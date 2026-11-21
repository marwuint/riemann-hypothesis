import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact _root_.GlobalTheory.TwV.Xc.scal_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (_root_.GlobalTheory.pairOK_allSites S hd)

end GlobalTheory.TwV
