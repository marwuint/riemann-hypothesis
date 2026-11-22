import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

end General

section Constructions

def prodAct (M M' : GKMod p q) : Mat p q →ₗ[ℂ] Module.End ℂ (M.V × M'.V) where
  toFun Z := LinearMap.prodMap (M.act Z) (M'.act Z)
  map_add' X Y := LinearMap.ext fun x => by simp
  map_smul' c X := LinearMap.ext fun x => by simp

theorem prodAct_apply (M M' : GKMod p q) (Z : Mat p q) (x : M.V × M'.V) :
    prodAct M M' Z x = (M.act Z x.1, M'.act Z x.2) := rfl

def prodMod (M M' : GKMod p q) : GKMod p q where
  V := M.V × M'.V
  act := prodAct M M'
  lie X Y := by
    apply LinearMap.ext; rintro ⟨x, x'⟩
    have h1 := LinearMap.congr_fun (M.lie X Y) x
    have h2 := LinearMap.congr_fun (M'.lie X Y) x'
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, prodAct_apply, h1, h2, Prod.mk_sub_mk]
  kfin := by
    rintro ⟨x, x'⟩
    obtain ⟨W, hW, hx, hs⟩ := M.kfin x
    obtain ⟨W', hW', hx', hs'⟩ := M'.kfin x'
    haveI := hW; haveI := hW'
    refine ⟨LinearMap.range (LinearMap.prodMap W.subtype W'.subtype), inferInstance,
      ⟨(⟨x, hx⟩, ⟨x', hx'⟩), rfl⟩, ?_⟩
    rintro Z hZ _ ⟨⟨y, y'⟩, rfl⟩
    exact ⟨(⟨M.act Z y, hs Z hZ y y.2⟩, ⟨M'.act Z y', hs' Z hZ y' y'.2⟩), rfl⟩
  wts := by
    rintro ⟨x, x'⟩
    have h1 := map_wts (b := prodAct M M') (LinearMap.inl ℂ M.V M'.V)
      (fun Z v => by simp [prodAct_apply]) (M.wts x)
    have h2 := map_wts (b := prodAct M M') (LinearMap.inr ℂ M.V M'.V)
      (fun Z v => by simp [prodAct_apply]) (M'.wts x')
    have := add_mem h1 h2
    simpa using this

def subAct (M : GKMod p q) (U : Submodule ℂ M.V) (h : ∀ Z, ∀ x ∈ U, M.act Z x ∈ U) :
    Mat p q →ₗ[ℂ] Module.End ℂ U where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by ext x; simp [LinearMap.restrict_apply]
  map_smul' c X := by ext x; simp [LinearMap.restrict_apply]

def subMod (M : GKMod p q) (U : Submodule ℂ M.V) (h : ∀ Z, ∀ x ∈ U, M.act Z x ∈ U) : GKMod p q where
  V := U
  act := subAct M U h
  lie X Y := by
    ext x
    have := LinearMap.congr_fun (M.lie X Y) (x : M.V)
    simpa [subAct, LinearMap.restrict_apply] using this
  kfin v := by
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    haveI := hW
    refine ⟨W.comap U.subtype, ?_, hv, fun X hX w hw => hs X hX w hw⟩
    exact Module.Finite.of_injective
      (U.subtype.restrict (p := W.comap U.subtype) (q := W) (fun x hx => hx))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
  wts v := by
    have h1 := GlobalTheory.BlockReps.decomp (act := M.act) (W := U) (fun Z _ w hw => h Z w hw) v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, U ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (subAct M U h) μ).map U.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [subAct, LinearMap.restrict_apply] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) : GKMod p q where
  V := M.V ⧸ N
  act :=
    { toFun := fun Z => N.mapQ N (M.act Z) fun y hy => hN Z y hy
      map_add' := fun Y Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp }
  lie := fun Y Z => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    have := LinearMap.congr_fun (M.lie Y Z) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.sub_apply, Module.End.mul_apply, this, Submodule.Quotient.mk_sub]
  kfin := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hv, hst⟩ := M.kfin v
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hv, ?_⟩
    rintro Z hZ _ ⟨w, hw, rfl⟩
    exact ⟨M.act Z w, hst Z hZ w hw, rfl⟩
  wts := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    exact map_wts (b := _) N.mkQ (fun Z x => rfl) (M.wts v)

end Constructions

section Max

def qmap (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    X.V →ₗ[ℂ] (quotMod X U hU).V := U.mkQ

end Max

section Main

def incl (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    (subMod X U hU).V →ₗ[ℂ] X.V := U.subtype

theorem incl_act (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U)
    (Z : Mat p q) (x : (subMod X U hU).V) : incl X U hU ((subMod X U hU).act Z x) = X.act Z (incl X U hU x) :=
  rfl

def sndP (M M' : GKMod p q) : (prodMod M M').V →ₗ[ℂ] M'.V := LinearMap.snd ℂ M.V M'.V

def pairP (M M' : GKMod p q) (x : M.V) (x' : M'.V) : (prodMod M M').V := (x, x')

end Main

end GlobalTheory.CommonQuot
