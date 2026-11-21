import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTranslatesConvergentLiftDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStanding

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commutesWith_of_isSquareConst_of_triple (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound)
    {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hT : SquareTriple W t i j) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c := by
  intro M hM Θ Θ' hΘ F hF hFc hFl hA hB
  funext g₁
  obtain ⟨hBa, hBe⟩ := _root_.GlobalTheory.BigRoute.lift_eq_integral_kerBig hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  obtain ⟨z, hz, hSa, hSe⟩ := _root_.GlobalTheory.SmallRoute.exists_translates_lift hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  refine mul_left_cancel₀ hz ?_
  rw [Pi.smul_apply, smul_eq_mul, hBe, mul_left_comm, hSe, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hBa, hSa] with g hb hs
  have h := hc M hM Θ Θ' hΘ z g g₁ ⟨hb, hs⟩
  linear_combination F g * h

theorem commutesWith_of_isSquareConst (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T}
    {i j : Fin D.R.m} (hS : SquareStanding G t) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c :=
  commutesWith_of_isSquareConst_of_triple hWC hK hP hL (squareTriple_of_standing hL W t i j hS) hc

end GlobalTheory.FunObj

end
