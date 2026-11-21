import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsUniformLinksRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

theorem links2_of_rows : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.Rows → SingleIndexPlacesAreTwisted p → Links2 p := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hw
  obtain ⟨hU, hB, hR⟩ := _root_.GlobalTheory.BigOn.SplitRows.unif_baseLinks_rankRows D L hT Gi Gl Kc Y cX ex Csz p hr
  obtain ⟨hBar, hPin, hPh⟩ := _root_.GlobalTheory.BigOn.ompins_onto D L hT Gi Gl Kc Y cX ex Csz p hr
  exact ⟨_root_.GlobalTheory.BigOn.splitPartRealisationWithScalars_char_of_weak D L hT Gi Gl Kc Y cX ex Csz p hr.exAt hw, hr.ok.ok2, hU, hB, hR, hBar, hPin, hPh⟩

end GlobalTheory.BigOn
