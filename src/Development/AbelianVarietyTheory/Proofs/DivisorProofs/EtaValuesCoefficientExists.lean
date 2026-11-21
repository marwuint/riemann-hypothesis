import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩

theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl

end GlobalTheory.GalLift.BaseDatum

end
