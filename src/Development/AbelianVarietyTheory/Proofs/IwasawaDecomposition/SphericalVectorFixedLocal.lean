import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

theorem conjSplit_w (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    (conjSplit s).w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f f' : GAf L n → W) :
    NG.heckeD J Dset (f + f') = NG.heckeD J Dset f + NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : GAf L n → W,
      Function.support (fun cc : GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply]
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n)) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem tN_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite) {m : ℕ} (F : Fin m → GAf L n → W) :
    NG.tN J s ϖ k (∑ j, F j) = ∑ j, NG.tN J s ϖ k (F j) := by
  classical
  have key : ∀ t : Finset (Fin m), NG.tN J s ϖ k (∑ j ∈ t, F j) = ∑ j ∈ t, NG.tN J s ϖ k (F j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [NG.tN, heckeD_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [NG.tN]
      rw [heckeD_add L n J _ hfin, smul_add]
  exact key Finset.univ

theorem prod_eq_vieta (n : ℕ) (β : Multiset ℂ) (hn : Multiset.card β = n) :
    (β.map fun a => X - C a).prod = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * β.esymm k) * X ^ (n - k) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hn, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton,
    Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr (by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega) fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_assoc]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cls_heq {E : Type} [Field E] [NumberField E] {n : ℕ} {a b : HeightOneSpectrum (𝓞 E)} (h : a = b)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (a.adicCompletion E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (b.adicCompletion E)))
    (he : HEq σ.cl τ.cl) : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls τ) := by
  subst h
  exact heq_of_eq (congrArg (Sigma.mk n) (eq_of_heq he))

end

end GlobalTheory.HeckeFrob

end
