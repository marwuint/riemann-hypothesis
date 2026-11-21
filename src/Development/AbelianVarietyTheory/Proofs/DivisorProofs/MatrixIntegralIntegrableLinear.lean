import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

noncomputable section
namespace GlobalTheory.GamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem box_eq_standard_box (p q : ℕ) (c : kˣ) :
    box p q c = (GlobalTheory.LocMod.Inhab.box (Fin p) (Fin q) c : Set (Matrix (Fin p) (Fin q) k)) := rfl

end GlobalTheory.GamMul
