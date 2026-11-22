import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P (PP.under (𝓞 D.host.F))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

end GlobalTheory.TopVol.InKConj
