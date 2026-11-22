import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace GlobalTheory.CurveJet

variable {C : Type} [Field C] {dd m : ℕ}

def inT (σ : Type) (f : PowerSeries C) : MvPowerSeries (Option σ) C :=
  MvPowerSeries.subst (fun _ : Unit => (X none : MvPowerSeries (Option σ) C)) f

theorem inT_eq_rename (σ : Type) (f : PowerSeries C) :
    inT σ f = rename (fun _ : Unit => (none : Option σ)) f := by
  rw [inT, rename_eq_subst]
  rfl

theorem constantCoeff_inT (σ : Type) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (inT σ f) = 0 := by
  rw [inT_eq_rename, constantCoeff_rename]
  exact hf

theorem optionEquivLeft_inT (σ : Type) (f : PowerSeries C) :
    optionEquivLeft σ C (inT σ f) = PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries σ C) f := by
  classical
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]
  split_ifs with hμ
  · subst hμ
    let e : Unit ↪ Option σ := ⟨fun _ => none, fun _ _ _ => rfl⟩
    have he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n) := by
      rw [Finsupp.embDomain_single, Finsupp.optionElim_zero]
      rfl
    rw [he]
    exact coeff_embDomain_rename e f (Finsupp.single () n)
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hμ
    ext s
    have h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_some] at h1
    simpa using h1

theorem optionEquivLeft_rename_some {σ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    optionEquivLeft σ C (rename (some : σ → Option σ) f) = PowerSeries.C f := by
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    have he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ := by
      ext t
      cases t <;> simp
    rw [he]
    exact coeff_embDomain_rename _ f μ
  · rw [map_zero]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hn
    have h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_none] at h1
    exact h1

theorem pderiv_coeff_optionEquivLeft {σ : Type} (f : MvPowerSeries (Option σ) C) (n : ℕ) (s : σ) :
    pderiv C s (PowerSeries.coeff n (optionEquivLeft σ C f)) =
      PowerSeries.coeff n (optionEquivLeft σ C (pderiv C (some s) f)) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]
  have key : Finsupp.optionElim n (μ + Finsupp.single s 1) =
      Finsupp.optionElim n μ + Finsupp.single (some s) 1 := by
    ext t
    cases t <;> simp [Finsupp.single_apply]
  rw [key, Finsupp.optionElim_apply_some]

end GlobalTheory.CurveJet
