import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandInvariantAtSuccPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandFiniteDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedInnerIntegralAtFirstOfSplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QVal

theorem valQr_succ (D : D7) (r : ℕ) (IH : ValQr D r) : ValQr D (r + 1) := by
  intro ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨lc₁, lc₂, cl₁, cl₂, cl₃, cl₄, μ₁', ρ₁', μ₂', ρ₂', m₁, s₁, m₂, s₂, p₁, p₂, hN', hL, i₁, i₂, i₃, i₄, e₁, e₂, hred⟩ :=
    _root_.GlobalTheory.QRed.reduce D ψ σ S r Q hinj μ₁ ρ₁ μ₂ ρ₂ hN
  have hN'' := hN'
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := hN''
  have hL' := hL
  obtain ⟨b1, -, b3, -, b5, -, b7, -⟩ := hL'
  obtain ⟨co₁, co₂⟩ := _root_.GlobalTheory.QVal.LevCO.isCO_levJ_levB D ψ σ S r (fun i => Q i.succ) (hinj.comp (Fin.succ_injective _))
  obtain ⟨v1, v2, v3⟩ := _root_.GlobalTheory.QVal.Inv.pint_invariant D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨n1, n2⟩ := _root_.GlobalTheory.QCells.finite_cells D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  apply hred (integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)
  haveI := lc₁
  haveI := lc₂
  haveI : BorelSpace (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  exact _root_.GlobalTheory.IterPeel.iterated_integral_product_groups _ _ _ _ _ _ _ _ cl₁ cl₃ cl₂ cl₄ μ₁' m₁ μ₂' m₂ ρ₁' s₁ ρ₂' s₂ p₁ p₂ a1 b1 a3 b5 a2 b3 a4 b7 i₁ i₃ i₂ i₄
    e₁ e₂ _ _ _ _ co₁ (Q 0).co₁ co₂ (Q 0).co₂ (pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) v1 v2 v3 n1 n2
    (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) _
    (fun x y => _root_.GlobalTheory.QValInner.innerVal_iter2 D ψ hψ σ S r Q hinj m₁ s₁ m₂ s₂ hL c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH x.1 x.2 y.1 y.2)
    (_root_.GlobalTheory.QValOuter.outer D r IH ψ hψ σ S Q hinj μ₁' ρ₁' μ₂' ρ₂' hN' c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH)

theorem valQ : ∀ D : D7, ValQ D := fun D => valQ_of_valQr D fun r => by
  induction r with
  | zero => exact _root_.GlobalTheory.QVal.valQr_zero D
  | succ r ih => exact valQr_succ D r ih

end GlobalTheory.QVal
end
