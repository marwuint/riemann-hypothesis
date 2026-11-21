import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipliStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColFockRed

open GlobalTheory.Grid

theorem isContAut_cusp {D : D7} {θ : InfFam D} {N : Node D} (F : N.Cusp θ) (x : SmT N.M) :
    GlobalTheory.Unf.IsContAut N.V (F.1 x) := by
  have sm : ∀ {f : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → ∀ c : ℂ, GlobalTheory.Unf.IsContAut N.V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  have ad : ∀ {f g : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → GlobalTheory.Unf.IsContAut N.V g → GlobalTheory.Unf.IsContAut N.V (f + g) :=
    fun hf hg => ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  obtain ⟨G, hG⟩ := F
  show GlobalTheory.Unf.IsContAut N.V (G x)
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact sm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact ad hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ⟨fun _ _ _ => rfl, continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact ad (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact sm (h x) c

theorem xp_is {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R}
    (hG : G.Is) (k : ℕ) (hk : k ≤ D.R.m) : ∃ ν P, (G.Xp k).Is ν 0 P := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    rw [show (D.R.m - D.R.m + 1) / 2 = 0 by omega] at h
    exact ⟨_, _, h⟩
  | succ k => exact ⟨_, _, hG.spaces.X k hk⟩

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem measX_haar_fd {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColFockRed
