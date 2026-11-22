import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelation

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem cutG_mem_congGrp (V : HSp D) (I : Ideal (AE D)) (ε : AF D.host.F) (hε : ε * ε = ε) {g : GA D V}
    (hg : g ∈ congGrp V I) : cutG V ε hε g ∈ congGrp V I := by
  rw [mem_congGrp_iff] at hg ⊢
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hg i j)

theorem grpAt_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  intro g hg
  rw [mem_grpAt_iff_parts] at hg ⊢
  exact fun i j => ⟨(hg i j).1, fun w hw => (hg i j).2 w fun h' => hw (h w h')⟩

theorem grpAt_inf_le (V : HSp D) (Q P R : Pl D → Prop) (h : ∀ p, Q p → ¬ P p → R p) {g : GA D V}
    (h1 : g ∈ grpAt V Q) (h2 : g ∈ grpAt V fun p => ¬ P p) : g ∈ grpAt V R := by
  rw [mem_grpAt_iff_parts] at h1 h2 ⊢
  refine fun i j => ⟨(h1 i j).1, fun w hw => ?_⟩
  by_cases hQ : Q w
  · by_cases hP : P w
    · exact (h2 i j).2 w (not_not.2 hP)
    · exact absurd (h w hQ hP) hw
  · exact (h1 i j).2 w hQ

theorem locHom_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y)
    {P : Pl D → Prop} (hP : P q.v) {g : GA D V} (hg : g ∈ grpOff V P) : GlobalTheory.LevIdx.locHom q V F g = 1 := by
  ext1
  rw [GlobalTheory.LevIdx.locHom_val, GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q hP hg, Matrix.mul_one, F.γβ]
  rfl

end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end

