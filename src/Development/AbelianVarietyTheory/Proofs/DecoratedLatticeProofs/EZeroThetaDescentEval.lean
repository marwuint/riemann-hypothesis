import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV

theorem good_fix {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (w : Fin (B.nV ℓ) → K) :
    ∑ g, (idemOf ℓ.X).coeff g • B.r g (B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w)) =
      B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w) := by
  set z := B.vE ℓ *ᵥ w with hz
  have hmem : z ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
    have e := (image_idempotent_spec K _ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
    rw [← e]
    exact ⟨w, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have hid := (idempotent_central K G ℓ.X hX).1
  have hhom := group_action_matrix_hom K B.S G B.r
  have hfix : B.S.gaMat B.r (idemOf ℓ.X) *ᵥ z = z := by
    rw [← hy]
    change B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y) = B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y
    rw [Matrix.mulVec_mulVec, ← hhom.2, goodAt, ← mul_assoc, hid]
  have hconv : ∀ (a : MonoidAlgebra K G) (x : Fin B.S.dim → K),
      B.S.basis.equivFun.symm (B.S.gaMat B.r a *ᵥ x) = ∑ g, a.coeff g • B.r g (B.S.basis.equivFun.symm x) := by
    intro a x
    apply B.S.basis.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp only [CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec, map_smul, CSD.actMat]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    have := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm x)
    rw [Module.Basis.equivFun_apply]
    rw [← this]
    congr 1
    funext i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← hconv, hfix]

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev

set_option maxHeartbeats 1000000 in

theorem thDn_act (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (v : (R.MY 0).Vec) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) (PiTensorProduct.tprod ℂ v) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
  have hS : ∀ j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hCR (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hred hM.jX t g x).elim fun κ' hκ' => ?_
  refine (GlobalTheory.ChainLiftEquiv.liftsExist_chain R h t 0 (lt_of_lt_of_le two_pos D.R.two_le_m) (R.eG g)).elim fun κ hκ => ?_
  exact funext fun y =>
    (GlobalTheory.ChainLiftEquiv.thDn_shift R h hM hC t hS (R.eG g) κ' hκ'.1 (R.jX t x) (R.jX t ((A.fam.R t).r g x)) hκ'.2 κ hκ _ y).trans
      (GlobalTheory.ChainLiftEquiv.actL_zero R t (R.eG g) κ hκ _ (GlobalTheory.ChainLiftEquiv.thDn_type R t _ v) y).symm

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev

set_option maxHeartbeats 1000000 in

theorem goodProjector_fixes_compositeThetaLift_of_fixed (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0)
    (x : A.fam.amb.FR t) (hx : ∑ g, (idemOf A.X).coeff g • A.fam.amb.opR t (Sum.inr g) x = x) (v : (R.MY 0).Vec) :
    R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) = R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) := by
  have key : R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) = R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
    conv_lhs => rw [← hx]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
    simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    exact congrArg (fun z => RealDat.eC (A := A) D.what₂.embLL g • z) (thDn_act hCR R h hM hC hred t g x v)
  exact key.symm

end GlobalTheory.GoodFix

