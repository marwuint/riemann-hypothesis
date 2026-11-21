import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Module.End
open scoped InnerProductSpace

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_iInf_eigenspace_eq_top [FiniteDimensional ℂ E] (T : I → E →ₗ[ℂ] E) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → E →ₗ[ℂ] E := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

end Abstract

section Form

variable {X I : Type} [AddCommGroup X] [Module ℂ X]

structure IsPosOn (Y : Submodule ℂ X) (B : X → X → ℂ) : Prop where
  lin : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  symm : ∀ x ∈ Y, ∀ y ∈ Y, B y x = star (B x y)
  pos : ∀ x ∈ Y, x ≠ 0 → 0 < (B x x).re

variable {Y : Submodule ℂ X} {B : X → X → ℂ}

theorem IsPosOn.zero_right (h : IsPosOn Y B) {x : X} (hx : x ∈ Y) : B x 0 = 0 := by
  have := h.lin x hx 0 Y.zero_mem 0 Y.zero_mem 1
  simpa using this

theorem IsPosOn.add_right (h : IsPosOn Y B) {x y z : X} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y) :
    B x (y + z) = B x y + B x z := by
  simpa using h.lin x hx y hy z hz 1

theorem IsPosOn.smul_right (h : IsPosOn Y B) {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) (c : ℂ) :
    B x (c • z) = c * B x z := by
  simpa [h.zero_right hx] using h.lin x hx 0 Y.zero_mem z hz c

@[reducible] def IsPosOn.core (h : IsPosOn Y B) : InnerProductSpace.Core ℂ Y where
  inner x y := B x y
  conj_inner_symm x y := (h.symm y y.2 x x.2).symm
  re_inner_nonneg x := by
    by_cases hx : (x : X) = 0
    · show 0 ≤ (B x x).re
      rw [hx, h.zero_right Y.zero_mem]; simp
    · exact (h.pos x x.2 hx).le
  add_left x y z := by
    show B ((x : X) + y) z = B x z + B y z
    rw [h.symm z z.2 _ (Y.add_mem x.2 y.2), h.add_right z.2 x.2 y.2, h.symm z z.2 x x.2, h.symm z z.2 y y.2, star_add]
  smul_left x y r := by
    show B (r • (x : X)) y = starRingEnd ℂ r * B x y
    rw [h.symm y y.2 _ (Y.smul_mem r x.2), h.smul_right y.2 x.2, h.symm y y.2 x x.2, star_mul']
    rfl
  definite x hx := by
    by_contra h0
    have := h.pos x x.2 (fun e => h0 (Subtype.ext e))
    have hx' : B x x = 0 := hx
    rw [hx'] at this
    simp at this

theorem IsPosOn.le_iSup_eigen [FiniteDimensional ℂ Y] (h : IsPosOn Y B) (T : I → X →ₗ[ℂ] X)
    (hT : ∀ i, ∀ x ∈ Y, T i x ∈ Y) (hc : ∀ i k, ∀ x ∈ Y, T i (T k x) = T k (T i x))
    (hadj : ∀ i, ∃ k, ∀ x ∈ Y, ∀ y ∈ Y, B (T i x) y = B x (T k y))
    (Z : Submodule ℂ X) (hZ : ∀ (χ : I → ℂ), ∀ x ∈ Y, (∀ i, T i x = χ i • x) → x ∈ Z) : Y ≤ Z := by
  letI := h.core
  letI : NormedAddCommGroup Y := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ Y := InnerProductSpace.ofCore _
  have key := iSup_iInf_eigenspace_eq_top (E := Y) (fun i => (T i).restrict (hT i))
    (fun i k => LinearMap.ext fun x => Subtype.ext (hc i k x x.2))
    (fun i => (hadj i).imp fun k hk x y => hk x x.2 y y.2)
  have : (⊤ : Submodule ℂ Y) ≤ Z.comap Y.subtype := by
    rw [← key]
    refine iSup_le fun χ x hx => hZ χ x x.2 fun i => ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    exact congrArg Subtype.val (hx i)
  exact fun x hx => this (x := ⟨x, hx⟩) Submodule.mem_top

end Form

end GlobalTheory.HeckeOrthSum
