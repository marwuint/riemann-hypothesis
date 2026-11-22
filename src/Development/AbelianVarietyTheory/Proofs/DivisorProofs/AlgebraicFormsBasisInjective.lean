import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistChoiceExample
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GoodLiftPhase
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations

noncomputable section

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

namespace GlobalTheory.TwistPlacesObj

open GlobalTheory.QPosCompare

section Lin

variable {K X E W : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {σ : K →+* ℂ} {j : X →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)

theorem lin_injective (hj : IsForm j) {n : ℕ} (f : (Fin n → K) →ₗ[K] X) (hf : Function.Injective f)
    (hZ : ∀ y, j (f y) ∈ LinearMap.range (LinearMap.adjoint θ)) :
    Function.Injective (Formalism.IndefR.Cx.lin fun k => θ (j (f (Pi.single k 1)))) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 : LinearIndependent K fun k : Fin n => f (Pi.single k 1) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    simpa [Function.comp_def] using this
  have h2 := hj.linInd h1
  set u : E := ∑ k, c k • j (f (Pi.single k 1)) with hu
  have h3 : u ∈ LinearMap.ker θ := by
    rw [Formalism.IndefR.Cx.lin_apply] at hc
    rw [LinearMap.mem_ker, hu, map_sum]
    simpa only [map_smul] using hc
  have h4 : u ∈ (LinearMap.ker θ)ᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ _)
  have h5 : u = 0 := inner_self_eq_zero.1 (h4 u h3)
  funext k
  exact Fintype.linearIndependent_iff.1 h2 c h5 k

variable {G : Type} [Group G] [Fintype G] (r : Representation K G X) (ρ : G → W →ₗ[ℂ] W)

end Lin

section Block

open Formalism.DivisionValues Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)
  {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {j : B.S.Forms →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)
  (ρ : G → W →ₗ[ℂ] W)

theorem toF_mem (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z :=
  (B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y)

end Block

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isForm_tw {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ σ' : K →+* ℂ} (s : Bool) (h : ∀ a, σ' a = cj s (σ a)) {j : X →ₛₗ[σ] E} (hj : IsForm j) :
    IsForm (E := Tw s E) (Tw.semi s h j) := by
  obtain ⟨⟨n, b, h1, h2⟩, h3⟩ := hj
  refine ⟨⟨n, b, (Tw.linInd (E := E) s h1 :), ?_⟩, fun x y => ?_⟩
  · have e : Set.range (Tw.semi s h j) = Tw.mk s '' Set.range j := by rw [← Set.range_comp]; rfl
    rw [e, tw_span, h2]
    rfl
  · obtain ⟨a, ha⟩ := h3 x y
    exact ⟨a, (congrArg (cj s) ha).trans (h a).symm⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable {R F}

open GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

end Real

end GlobalTheory.TwistPlacesObj

end
