import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatible

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section GenericCmp

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L,
    d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  set v := Module.finBasis (FractionRing O) M
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← v.sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_eq_smul_of_read
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (s t : L ⊗[O] M) (a : ℂ) (h : readExt rd eL hL s = a • readExt rd eL hL t) (h0 : readExt rd eL hL s ≠ 0) :
    ∃ b : L, eL b = a ∧ s = b • t := by
  set R := readExt rd eL hL with hR
  set v := Module.finBasis (FractionRing O) M
  have hne : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsm : ∀ (d : O) (x : L ⊗[O] M), R (d • x) = eL (algebraMap O L d) • R x := fun d x => by
    rw [← algebraMap_smul L d x, hR, readExt_smul]
  have hsum : ∀ c : _ → L, R (∑ k, c k ⊗ₜ v k) = ∑ k, eL (c k) • rd (v k) := fun c => by
    rw [map_sum]
    rfl
  obtain ⟨d, hd, c, es⟩ := exists_smul_eq_sum_finBasis s
  obtain ⟨d', hd', c', et⟩ := exists_smul_eq_sum_finBasis t
  have hcoef : ∀ k, eL (algebraMap O L d') * eL (c k) = a * (eL (algebraMap O L d) * eL (c' k)) := fun k => by
    have e1 : ∑ k, (eL (algebraMap O L d') * eL (c k) - a * (eL (algebraMap O L d) * eL (c' k))) • rd (v k) = 0 := by
      have h1 : eL (algebraMap O L d') • R (d • s) = a • eL (algebraMap O L d) • R (d' • t) := by
        rw [hsm, hsm, h]
        simp only [smul_smul]
        congr 1
        ring
      rw [es, et, hsum, hsum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [h1, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ e1 k)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    have h2 : eL (algebraMap O L d) • R s = 0 := by
      rw [← hsm, es, hsum]
      simp [hc]
    exact (smul_eq_zero.1 h2).resolve_left (hne d hd)
  have hl : eL (algebraMap O L d') * eL (c k) ≠ 0 := mul_ne_zero (hne d' hd') ((map_ne_zero eL).2 hk)
  have hr : eL (algebraMap O L d) * eL (c' k) ≠ 0 := fun h3 => hl (by rw [hcoef k, h3, mul_zero])
  refine ⟨(algebraMap O L d' * c k) / (algebraMap O L d * c' k), ?_, ?_⟩
  · rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
  · have hb : eL ((algebraMap O L d' * c k) / (algebraMap O L d * c' k)) = a := by
      rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
    apply readExt_injective rd eL hL hF
    rw [readExt_smul, hb, ← hR, h]

end GenericCmp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.SerBase

end GlobalTheory.BigOn.Exp.SerBase
