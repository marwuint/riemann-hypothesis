import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.JoinLinked

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0')
    (Φ : ∀ F : (∀ u, Formalism.L2.Forms.Forms0 D u), ∀ P : GlobalTheory.Mem.SRe.SPack D F, GlobalTheory.Mem.SRe.SRest P → Formalism.L2.Theta.GA D (D.sp.Y 0) → ℝ → Prop)
    {P' : GlobalTheory.Mem.SRe.SPack D F0'} {S' : GlobalTheory.Mem.SRe.SRest P'} {t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)} {c c' : ℝ}
    {P : GlobalTheory.Mem.SRe.SPack D F0} {S : GlobalTheory.Mem.SRe.SRest P} (hP : HEq P P') (hS : HEq S S') (ht : HEq t t') (hc : c = c')
    (h : Φ F0' P' S' t' c') : Φ F0 P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq ht
  subst hc
  exact h

theorem schurAll (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) :
    Formalism.IndefR.Links.SchurAll D :=
  fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2

end GlobalTheory.Fc.JoinLinked

end
