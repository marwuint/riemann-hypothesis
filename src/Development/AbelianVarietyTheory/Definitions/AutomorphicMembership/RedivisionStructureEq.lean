import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure New (D : D7) : Type 1 where
  Z : SNew D
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ

def reD (D : D7) (Z : New D) : D7 := GlobalTheory.EX.OB.setDiv (reS D Z.Z) Z.N Z.h

set_option maxHeartbeats 4000000 in

def SameForms0LevelsAndValues {D : D7} (Z : New D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reD D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

variable {D : D7} (Z : New D)

def wd (u : D.what₂.Word) : (reD D Z).what₂.Word := u

def New.self (D : D7) : New D := ⟨SNew.self D, fun u => (D.div.Nu u).L, D.div.h⟩

def New.ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : New D := ⟨SNew.self D, N, h⟩

instance instInhabitedNew (D : D7) : Inhabited (New D) := ⟨New.self D⟩

set_option maxHeartbeats 4000000 in

def reX (X : HidaSetting D) : HidaSetting (reD D Z) := { X with }

end GlobalTheory.Mem.SRe

end
