import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.SeeSaw.LocTarget

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y : Type} [Fintype Y] [DecidableEq Y] {S : HSp D} (F : GlobalTheory.LocMod.Frame k S.rank Y) : p.IsLoc F 1 1 := by
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero], ?_⟩
  rw [h1, Units.val_one, Matrix.mul_one, F.βγ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isComp_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]

theorem om_phi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j b : ℕ) (H : j + b = s) (hb : j + 1 + b = s + 1)
    (x : ((S.T t).lev (j + 1) b hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) 1 x.1 ((S.T t).Phi j b H) =
      ((((S.T t).lev (j + 1) b hb).lam x : ℂ))⁻¹ • (S.T t).Phi j b H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hL : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  obtain ⟨hJ, hl⟩ := h2 (j + 1) b hb
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev (j + 1) b hb).J := by rw [hJ]; exact x.2
  have := (hL.1 j b H).2 ⟨x.1, hx⟩
  rw [h1, hl x.1 hx x.2, Units.val_inv_eq_inv_val] at this
  exact this

end GlobalTheory.SeeSaw.LocTarget
