import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
namespace GlobalTheory.MtId
variable {D : D7}
section State
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
variable {P : Pre2 K w} (x : St P)
theorem exists_matrix_input_identity_frame_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ w P x =>
    ∃ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), ∀ i, GlobalTheory.MtRead.IdFrame x.r.Y.hF (m.ad.PV i) :=
  fun _ => StepW.of_all fun _ _ _ _ _ _ _ hs _ x => hs.1.elim fun pin => inMt_state x pin
end State
end GlobalTheory.MtId
end
end
end
