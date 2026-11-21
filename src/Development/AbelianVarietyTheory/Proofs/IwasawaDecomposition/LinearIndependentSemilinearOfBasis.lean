import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFramesNormAtEqNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemilinearBasisImageIndepOfBasis

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem linearIndependent_semilinear_of_basis {K : Type} [Field K] (e : K →+* ℂ) {V : Type} [AddCommGroup V]
    [Module K V] {W : Type} [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) {ι κ : Type}
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun i => j (b i))) (v : κ → V)
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => j (v i)) := by
  classical
  set S : Submodule ℂ W := Submodule.span ℂ (Set.range fun i => j (b i)) with hS
  have hmem : ∀ x, j x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
  let j' : V →ₛₗ[e] S := j.codRestrict S hmem
  have h1 : LinearIndependent ℂ (fun i => j' (b i)) :=
    LinearIndependent.of_comp S.subtype hb
  have h2 : Submodule.span ℂ (Set.range fun i => j' (b i)) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  let b' := Module.Basis.extend (hv.linearIndepOn_id)
  have h3 := (GlobalTheory.semilinear_basis_image_indep_of_basis K e V S j' ι _ b b' ⟨h1, h2⟩).1
  have h4 := h3.map' S.subtype S.ker_subtype
  let f : κ → (hv.linearIndepOn_id).extend (Set.subset_univ _) := fun i =>
    ⟨v i, (hv.linearIndepOn_id).subset_extend _ ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hv.injective (congrArg Subtype.val h)
  have h5 := h4.comp f hf
  have h6 : (fun i => j (v i)) = (⇑S.subtype ∘ fun i => j' (b' i)) ∘ f := by
    funext i
    simp [b', f, j', Module.Basis.extend_apply_self]
  rw [h6]
  exact h5

def coordForm {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem coordForm_basisFun {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) (i : Fin n) : coordForm e c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  show ∑ k, e (Pi.basisFun K (Fin n) i k) • c k = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

def ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) :
    (C.fm u).ramSub →ₛₗ[B.embLL] W.Mu u where
  toFun x := (W.eMu u).symm ⟨(C.fm u).emb 0 x, x.2⟩
  map_add' x y := by
    rw [← map_add]; congr 1; ext1; simp
  map_smul' a x := by
    rw [← map_smul]; congr 1; ext1; simp [map_smulₛₗ]

theorem eMu_ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) (x : (C.fm u).ramSub) :
    ((W.eMu u (ramForm W u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) =
      (C.fm u).emb 0 x := by
  show ((W.eMu u ((W.eMu u).symm _) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ramForm_basis {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) {κ : Type}
    (b : Module.Basis κ B.LL (C.fm u).ramSub) :
    LinearIndependent ℂ (fun i => ramForm W u (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) = ⊤ := by
  let g : W.Mu u →ₗ[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) :=
    (C.mem u).A.Mram.subtype ∘ₗ (W.eMu u).toLinearMap
  have hg : ∀ x, g (ramForm W u x) = (C.fm u).emb 0 x := eMu_ramForm W u
  have hginj : Function.Injective g := (C.mem u).A.Mram.injective_subtype.comp (W.eMu u).injective
  constructor
  · apply LinearIndependent.of_comp g
    have := linearIndependent_semilinear_of_basis B.embLL ((C.fm u).emb 0) ((C.fm u).lat 0).b
      ((C.fm u).emb_basis 0).1 (fun i => ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V))
      (b.linearIndependent.map' (C.fm u).ramSub.subtype (Submodule.ker_subtype _))
    have h6 : (⇑g ∘ fun i => ramForm W u (b i)) =
        fun i => (C.fm u).emb 0 ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V) := funext fun i => hg _
    rw [h6]
    exact this
  · set S := Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) with hS
    have hmem : ∀ x, ramForm W u x ∈ S := by
      intro x
      have hx : x ∈ Submodule.span B.LL (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
      | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
    rw [eq_top_iff]
    intro φ _
    have h1 : g φ ∈ (C.mem u).A.Mram := (W.eMu u φ).2
    rw [← GlobalTheory.RamRational.span_ramSub_cols B C u] at h1
    have h2 : Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) ≤ S.map g := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hmem ⟨x, hx⟩, hg _⟩
    obtain ⟨ψ, hψ, hψ'⟩ := h2 h1
    rwa [← hginj hψ']

end GlobalTheory.Mem

end
