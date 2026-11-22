import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
structure LocalLanglandsHypothesis (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop where
  pr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt
  ser : SerN
  arch : _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL
  par : _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL
  pt : _root_.GlobalTheory.HeightCounting.Up.PointStatement hL
  parMem : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw)
end
end GlobalTheory.Mem.Top.Bl
end
end
end
