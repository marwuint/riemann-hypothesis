import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩

section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)

theorem hP_assemble_eq (p) : hP (assemble B C W V S N G) p = hP (assemble B C W' V' S' N' G') p := rfl

theorem lamRec_stages (u g) : lamRec (assemble B C W V S N G) u g = lamRec (assemble B C W' V' S' N' G') u g := rfl

theorem tauRec_stages (w : B.places.Pl) [h : Fact (B.places.resChar w).Prime] (n) :
    @tauRec (assemble B C W V S N G) w h n = @tauRec (assemble B C W' V' S' N' G') w h n := rfl

theorem omTied_stages (δ : ℂ) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W V S N G) δ ↔ Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W' V' S' N' G) δ := Iff.rfl

end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  ⟨fun h W V S N => ⟨(h W V S N).1, (h W V S N).2.2⟩,
    fun h W V S N => let ⟨a, ⟨t⟩⟩ := h W V S N; ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
