import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem levFn_datY_noQ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm) (x : GL (Fin V.rank) (Lev.EAf D)) :
    levFn β (Lev.datY V.rank r t j hr Pg Q P χ ξ fr) x = levFn β (Lev.datY V.rank r t j hr Pg ∅ P χ ξ' fr) x := by
  unfold levFn
  have hq : ∀ PP ∈ (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).Q,
      (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).xq PP
        (dBlk (blk2 (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r = r from rfl, Formalism.IndefR.Eqv.Act.block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.BaseChain

end
