import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkChart

theorem mem_HR_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig J ↔ adj (g.1 : Mx D k k) * rat J * g.1 = rat J := Iff.rfl

end GlobalTheory.SWLinkChart

end
