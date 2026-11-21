import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConcreteChainAgreesAtTupleOfNormalisedRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_atG_pinned : GlobalTheory.AtG.JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  intro hJ Bd Q Lk hQ
  exact _root_.GlobalTheory.AtG.row_atG_of_jetSplitAmb hJ Q Lk
    (RowE.of_all fun _ K β _ _ _ hq _ μ _ => _root_.GlobalTheory.Svd.tiesAt_of_rowPin K β (hQ _ _ _ _ _ hq) μ)

end GlobalTheory.AtG
