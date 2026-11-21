import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.SeeSaw.LocSrc

section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem valuation_det_of_mem_stabLat {Y : Type} [Fintype Y] [DecidableEq Y] {g h : GL Y k} (hh : h ∈ GlobalTheory.StepData.stabLat g) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  have h1 := valuation_det_of_mem_KO (GlobalTheory.StepData.mem_stabLat.1 hh)
  have e : Matrix.GeneralLinearGroup.det (g⁻¹ * h * g) = Matrix.GeneralLinearGroup.det h := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [e] at h1

theorem om_Phi {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j a : ℕ) (H : j + a = s) (hb : j + (a + 1) = s + 1)
    (x : ((S.T t).lev j (a + 1) hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) x.1 1 ((S.T t).Phi j a H) = (((S.T t).lev j (a + 1) hb).lam x : ℂ) • (S.T t).Phi j a H := by
  obtain ⟨e1, e2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev j (a + 1) hb).J := by rw [(e2 j (a + 1) hb).1]; exact x.2
  have L : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (L.1 j a H).1 ⟨x.1, hx⟩
  rw [e1, (e2 j (a + 1) hb).2 x.1 hx x.2] at h1
  exact h1

end Local

end GlobalTheory.SeeSaw.LocSrc
end
