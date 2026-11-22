import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowForm

section Abstract

variable {K X Y : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem exists_descent {H W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] {σ₁ σ₂ : K →+* ℂ} (e : σ₁ = σ₂)
    (φ : Y →ₛₗ[σ₁] W) (ψ : X →ₛₗ[σ₂] H) (T : H →ₗ[ℂ] W) (c : ℂ) (h : ∀ x, ∃! y, φ y = c • T (ψ x)) :
    ∃ θ : X →ₗ[K] Y, ∀ x, φ (θ x) = c • T (ψ x) := by
  subst e
  choose f hf hu using h
  refine ⟨⟨⟨f, fun x x' => (hu _ _ ?_).symm⟩, fun a x => (hu _ _ ?_).symm⟩, hf⟩
  · simp only [map_add, hf, smul_add]
  · simp only [map_smulₛₗ, hf, RingHom.id_apply, smul_comm c]

theorem mem_orth_ker [FiniteDimensional K X] {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {σ : K →+* ℂ} (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W)
    (U : W ≃ₗᵢ[ℂ] W) (g : W →ₗ[ℂ] W) (κ : ℂ) (h1 : Submodule.span ℂ (Set.range j) = ⊤)
    (h2 : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (h3 : ∀ x, U (jW (θ x)) = κ • g (th (j x))) {x : X} (h4 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0) :
    j x ∈ (LinearMap.ker th)ᗮ := by
  have key := GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW
    ((U.symm.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ (κ • (g ∘ₗ th))) h1 h2 fun x => by
      show U.symm (κ • g (th (j x))) = _
      rw [← h3, U.symm_apply_apply]
  have h5 : LinearMap.ker th ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := fun w hw => key (by
    show U.symm (κ • g (th w)) = 0
    rw [LinearMap.mem_ker.1 hw, map_zero, smul_zero, map_zero])
  refine Submodule.orthogonal_le h5 ((Submodule.mem_orthogonal' _ _).2 fun w hw => ?_)
  have h6 : Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) ≤ LinearMap.ker (innerₛₗ ℂ (j x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h4 u hu
  exact h6 hw

theorem re_inner_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem csumAt_conj [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    csumAt S ((starRingEnd ℂ).comp σ) f g = starRingEnd ℂ (csumAt S σ f g) := by
  unfold csumAt
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, RingHom.comp_apply]
  rfl

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem toF_mem (i : Fin D.R.m) (t : T0) (y : Fin ((A.fam.L i t).dZ (liftLvl F) (liftSub R F i t)) → D.what₂.LL) :
    (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y ∈ liftSub R F i t := by
  obtain ⟨f, hf, e⟩ : ((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y ∈
    (A.fam.L i t).Z0 (liftLvl F) (liftSub R F i t) := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y = f :=
    (congrArg (A.fam.L i t).S.basis.equivFun.symm e.symm).trans ((A.fam.L i t).S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem norm_wC (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (z : Fin (finrank D.what₂.LL (R.WL F false i)) → D.what₂.LL) :
    ‖(R.toCx F).wC false i v (cpt v.embedding z)‖ ^ 2 =
      (RealDat.nP F false)⁻¹ * ‖(R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z)‖ ^ 2 := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx F).wC false i v (cpt v.embedding z)) :
      R.WS F false i (sgAt D.what₂.embLL v)) : (R.HW i (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z) := by
    have e0 : (R.toCx F).wC false i v (cpt v.embedding z) = ∑ k, v.embedding (z k) • (R.toCx F).bW false i v k := rfl
    refine (congrArg (fun a => ((Tw.out (s := twAt D.what₂.embLL v) a : R.WS F false i (sgAt D.what₂.embLL v)) :
      (R.HW i (sgAt D.what₂.embLL v)).H)) e0).trans ?_
    refine (congrArg Subtype.val (out_sum _)).trans ((Submodule.coe_sum _ _ _).trans ?_)
    unfold coordMap
    rw [Fintype.linearCombination_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show cj (twAt D.what₂.embLL v) (v.embedding (z k)) •
      ((((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (R.bL F false i k)) = _
    rw [map_smulₛₗ, emb_eq D.what₂.embLL v, cj_cj, smul_comm]
  have e2 := congrArg norm e
  refine (congrArg (· ^ 2) e2).trans ?_
  show ‖_ • _‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (RealDat.nP_pos false).le]

end GlobalTheory.LowForm

end
