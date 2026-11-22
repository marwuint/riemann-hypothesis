import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffInh

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

section Empty

variable {P : Pl D → Prop}

theorem mem_GinfC_of_all (hP : ∀ v, P v) {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) : g ∈ GinfC S := by
  rw [grpOff, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hg
  rw [GinfC, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have e : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1 : Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P :=
    Ideal.Quotient.eq.1 ((hg i j).trans e.symm)
  have h2 := GlobalTheory.SelfDualAt.eq_zero_of_compFin (finPart D _) fun w => (Submodule.mem_iInf _).1 h1 ⟨w, hP w⟩
  rw [RingHom.map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Empty

end GlobalTheory.FinPl.OffInh

end
