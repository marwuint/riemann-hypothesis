import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB
open GlobalTheory.LB (resG_resG resG_self homOfLinear toMod fun_ext_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.TriangularFrames

variable {C : Scheme.{0}} {F : C.Modules} {J : Type} {T : J → C.Opens} {κ : J → Type}
  [∀ j, Fintype (κ j)] {v : ∀ j, κ j → Γ(F, T j)} {α : Type}

variable [Fintype α] {rk : α → ℕ} {e : ∀ j, α ↪ κ j}

variable {g : α → ∀ j j', Γ(C, T j ⊓ T j')}

def refine (M : LB C) (idx : J → M.ι) (hle : ∀ j, T j ≤ M.U (idx j)) : LB C where
  ι := J
  U := T
  g j j' := res (inf_le_inf (hle j) (hle j')) (M.g (idx j) (idx j'))

theorem isLB_refine (hT : ⨆ j, T j = ⊤) {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : (refine M idx hle).IsLB where
  cover := hT
  g_self j := by
    have hg : ((refine M idx hle).g j j).val =
        resG C (inf_le_inf (hle j) (hle j)) (M.g (idx j) (idx j)).val :=
      GlobalTheory.LB.val_res _ _
    have h0 := hM.g_self (idx j)
    rw [Units.ext_iff, GlobalTheory.LB.val_res, Units.val_one] at h0
    apply Units.ext
    rw [GlobalTheory.LB.val_res, hg]
    have h1 := congrArg (resG C (hle j)) h0
    rw [resG_resG, map_one] at h1
    exact (resG_resG _ _ _).trans h1
  cocycle i j k := by
    have hg : ∀ i j : J, ((refine M idx hle).g i j).val =
        resG C (inf_le_inf (hle i) (hle j)) (M.g (idx i) (idx j)).val :=
      fun i j => GlobalTheory.LB.val_res _ _
    have h0 := hM.cocycle (idx i) (idx j) (idx k)
    rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at h0
    apply Units.ext
    rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hg i j, hg j k, hg i k]
    have h1 := congrArg (resG C (inf_le_inf (inf_le_inf (hle i) (hle j)) (hle k))) h0
    rw [map_mul, resG_resG, resG_resG, resG_resG] at h1
    exact (congrArg₂ (· * ·) (resG_resG _ _ _) (resG_resG _ _ _)).trans
      (h1.trans (resG_resG _ _ _).symm)

private theorem res_transition_mul_comm_square {M : LB C} (hM : M.IsLB) (i i' k k' : M.ι) {W : C.Opens}
    (h₁ : W ≤ M.U i) (h₂ : W ≤ M.U i') (h₃ : W ≤ M.U k) (h₄ : W ≤ M.U k') :
    resG C (le_inf h₁ h₃) (M.g i k).val * resG C (le_inf h₃ h₄) (M.g k k').val =
      resG C (le_inf h₁ h₂) (M.g i i').val * resG C (le_inf h₂ h₄) (M.g i' k').val := by
  have c1 := hM.cocycle i k k'
  have c2 := hM.cocycle i i' k'
  rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at c1 c2
  have d1 := congrArg (resG C (le_inf (le_inf h₁ h₃) h₄)) c1
  have d2 := congrArg (resG C (le_inf (le_inf h₁ h₂) h₄)) c2
  rw [map_mul, resG_resG, resG_resG, resG_resG] at d1 d2
  exact d1.trans d2.symm

theorem lbIso_refine {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : LBIso (refine M idx hle) M := by
  have grp : ∀ {R : Type} [CommRing R] (X A B Y : Rˣ), X * B = A * Y → X = A * B⁻¹ * Y := by
    intro R _ X A B Y h
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, h]
  have hv2 : ∀ {U V W : C.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(C, U)ˣ),
      ((res h' (res h u) : Γ(C, W)ˣ) : Γ(C, W)) = resG C (h'.trans h) (u : Γ(C, U)) := by
    intro U V W h h' u
    rw [GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, resG_resG]
  refine ⟨⟨fun p => res (show M.U p.1 ⊓ T p.2 ≤ M.U p.1 ⊓ M.U (idx p.2) from
    inf_le_inf le_rfl (hle p.2)) (M.g p.1 (idx p.2))⟩, ?_⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩
  apply grp
  apply Units.ext
  have key := res_transition_mul_comm_square hM i i' (idx j) (idx j') (W := (M.U i ⊓ T j) ⊓ (M.U i' ⊓ T j'))
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    ((inf_le_left.trans inf_le_right).trans (hle j)) ((inf_le_right.trans inf_le_right).trans (hle j'))
  exact ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) (hv2 _ _ _) (hv2 _ _ _)).trans
    (key.trans (congrArg₂ (· * ·) (GlobalTheory.LB.val_res _ _).symm (hv2 _ _ _).symm)))).trans
    (Units.val_mul _ _).symm

end GlobalTheory.TriangularFrames

namespace GlobalTheory.TriangularFrames

end GlobalTheory.TriangularFrames
