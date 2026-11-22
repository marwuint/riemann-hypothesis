import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataChainStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataTopStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumCombinationsDifferByScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.GVecAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem comb_zero (c : WO S T →₀ ℂ) : comb ψ S T c 0 = 0 := by
  have := comb_smul (ψ := ψ) c 0 0
  rwa [zero_smul, zero_smul] at this

theorem comb_pureTensorO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {d o e : WO S T →₀ ℂ} {g : WO S T → ℂ} {s : ℂ} (hd : IsFinComb d) (ho : IsFinComb o) (he : IsFinComb e)
    (hg : IsThetaFunO ψ S T g) {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T)
    (h : om (b, b') (comb ψ S T d g) = s • comb ψ S T e (comb ψ S T o (om (b, b') g))) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a * b, a' * b') (comb ψ S T d (pureTensorO ψ θ S T sS sT BS BT g P)) =
      s • comb ψ S T e (comb ψ S T o (om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT g P))) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hfin : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧
      om (b, b') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (b, b') f) P := fun f hf =>
    GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hbg := hW.om_pres (b, b') g hg
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
  have t1 : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P) := (hfin _ hbg).1
  have t2 : IsThetaFunO ψ S T (comb ψ S T o (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P)) := theta_comb hψ ho t1
  rw [e1, map_mul, Module.End.mul_apply, Module.End.mul_apply, comb_pureTensorO hψ hθ sS sT BS BT hd hg,
    (hfin _ (theta_comb hψ hd hg)).2, h, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, (hfin g hg).2,
    ← comb_pureTensorO hψ hθ sS sT BS BT he (theta_comb hψ ho hbg), ← comb_pureTensorO hψ hθ sS sT BS BT ho hbg,
    GlobalTheory.FrComb.om_comb hW ha ha' he t2, GlobalTheory.FrComb.om_comb hW ha ha' ho t1]

theorem pureTensorO_zero (sS sT BS BT) (P) : pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) P = 0 := by
  have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
  rwa [zero_smul, zero_smul] at this

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end Gen

end GlobalTheory.GVecAt

namespace GlobalTheory.GVecAt

theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := _root_.GlobalTheory.VacScalar.main

end GlobalTheory.GVecAt
