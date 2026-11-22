import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamSplit

theorem stepVecOf_unique {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f)
    (h' : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f') : f = f' := by
  obtain ⟨-, e, he, hθ⟩ := h
  obtain ⟨-, e', he', hθ'⟩ := h'
  obtain rfl := GlobalTheory.DatumFourier.idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm, hθ'.2 Tm hTm]

end GlobalTheory.FamSplit

namespace GlobalTheory.FamSplit

end GlobalTheory.FamSplit
