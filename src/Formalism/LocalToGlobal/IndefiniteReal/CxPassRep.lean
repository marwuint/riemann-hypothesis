import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

def cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : Fin B.S.dim → K :=
  (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)

theorem toF_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y = B.S.basis.equivFun.symm (cv B ℓ Z y) := rfl

theorem cv_injective (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) : Function.Injective (cv B ℓ Z) := by
  intro x y h
  exact (subspace_image_spec K _ (B.Z0 ℓ Z)).1
    ((image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).1 h)

theorem mem_coord (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    w ∈ B.coord Z ↔ B.S.basis.equivFun.symm w ∈ Z := by
  unfold BlockDat.coord
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa using hf
  · intro h
    exact ⟨_, h, B.S.basis.equivFun.apply_symm_apply w⟩

theorem range_cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    (∃ y, cv B ℓ Z y = w) ↔ w ∈ B.coord Z ∧ w ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
      rw [← hs]
      exact ⟨y, rfl⟩
    exact ⟨hy, ⟨_, rfl⟩⟩
  · rintro ⟨hZ, u, rfl⟩
    have hu : u ∈ B.Z0 ℓ Z := hZ
    rw [← hs] at hu
    obtain ⟨y, rfl⟩ := hu
    exact ⟨y, rfl⟩

theorem range_vE_bot (X : Finset (G → K)) :
    LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin = LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X (⊥ : Subgroup G) 1))).2
  have hb : goodAt X (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = idemOf X := by
    unfold goodAt
    rw [level_idempotent_bot K G, mul_one]
  rw [← hb]
  exact h

theorem range_vE_le (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin ≤ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
  rw [range_vE_bot]
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X P ψ))).2
  change LinearMap.range (imE (B.S.gaMat B.r (goodAt X P ψ))).mulVecLin ≤ _
  rw [h]
  unfold goodAt
  rw [(group_action_matrix_hom K B.S G B.r).2, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem range_vE_lvl (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin ⊓ B.S.lvlPart B.r P ψ :=
  good_part_spec K B.S G B.r X hX P ψ

theorem actMat_coord (g : G) (w : Fin B.S.dim → K) :
    (B.S.actMat B.r g).mulVec w = B.S.basis.equivFun (B.r g (B.S.basis.equivFun.symm w)) := by
  have h := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm w)
  have hx : (B.S.basis.repr (B.S.basis.equivFun.symm w) : Fin B.S.dim → K) = w := by
    rw [← Basis.equivFun_apply]
    exact B.S.basis.equivFun.apply_symm_apply w
  rw [hx] at h
  unfold CSD.actMat
  rw [h, Basis.equivFun_apply]

theorem coord_act (Z : Submodule K B.S.Forms) (g : G) (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (w : Fin B.S.dim → K)
    (hw : w ∈ B.coord Z) : (B.S.actMat B.r g).mulVec w ∈ B.coord Z := by
  rw [mem_coord] at hw ⊢
  rw [actMat_coord, LinearEquiv.symm_apply_apply]
  exact hZ _ hw

theorem gaMat_single (g : G) : B.S.gaMat B.r (MonoidAlgebra.single g 1) = B.S.actMat B.r g := by
  rw [CSD.gaMat_eq_lift, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem comm_idem (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (a : MonoidAlgebra K G) :
    B.S.gaMat B.r a * B.S.gaMat B.r (idemOf X) = B.S.gaMat B.r (idemOf X) * B.S.gaMat B.r a := by
  have hm := (group_action_matrix_hom K B.S G B.r).2
  rw [← hm, ← hm, (idempotent_central K G X hX).2 a]

theorem toF_act (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (g : G)
    (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (x : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    ∃ y, B.toF ⟨X, ⊥, 1⟩ Z y = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) := by
  obtain ⟨hZx, hV⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨x, rfl⟩
  rw [range_vE_bot] at hV
  obtain ⟨w, hw⟩ := hV
  have h1 : (B.S.actMat B.r g).mulVec (cv B ⟨X, ⊥, 1⟩ Z x) ∈ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
    rw [range_vE_bot]
    refine ⟨(B.S.actMat B.r g).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hw ⊢
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← gaMat_single, comm_idem B X hX]
  obtain ⟨y, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).2 ⟨coord_act B Z g hZ _ hZx, h1⟩
  refine ⟨y, ?_⟩
  rw [toF_eq, toF_eq, hy, actMat_coord, LinearEquiv.symm_apply_apply]

end Block

section Rel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases h : i = k <;> simp [cpt, h]

theorem relK (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (g : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hg : ∀ x : Fin n → K, ∃ y : Fin D → K, f (cpt σ y) = g (cpt σ x)) :
    IsRat σ (relMat f g) ∧ ∀ x : Fin n → K, f (cpt σ ((kMat σ (relMat f g)).mulVec x)) = g (cpt σ x) := by
  have hk : ∀ k, g (Pi.single k 1) ∈ LinearMap.range f := fun k => by
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    exact ⟨_, hy⟩
  have hrat : IsRat σ (relMat f g) := by
    intro i k
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    have hs : solve f (g (Pi.single k 1)) = cpt σ y := hf (by rw [solve_spec f (hk k), hy])
    exact ⟨y i, by simp only [relMat, Matrix.of_apply, hs, cpt]⟩
  refine ⟨hrat, fun x => ?_⟩
  rw [cpt_mulVec, kMat_map σ hrat, relMat_spec f g hk]

theorem key_row' {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (hr : ∀ t, LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b Bs.μ0)) (hq : X.RATmu cr b)
    (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec x)) = X.iC cr b t (cpt Bs.v0.embedding x) := by
  rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hq t)]
  refine relMat_spec _ _ (fun k => ?_) _
  rw [← hr t]
  exact ⟨_, rfl⟩

end Rel

section Block2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

theorem range_eq_block (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms)
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, cv B ⟨X, ⊥, 1⟩ Z (J.mulVec x) = cv B ⟨X, P, ψ⟩ Z x)
    (Ep : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hE : ∀ y, cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) =
      (B.S.gaMat B.r (lvlIdem P ψ)).mulVec (cv B ⟨X, ⊥, 1⟩ Z y)) :
    LinearMap.range J.mulVecLin = LinearMap.range Ep.mulVecLin := by
  have hinj := cv_injective B ⟨X, ⊥, 1⟩ Z
  have hlvl := range_vE_lvl B X hX P ψ
  ext z
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨J.mulVec x, hinj ?_⟩
    rw [hE, hJ]
    have hx : cv B ⟨X, P, ψ⟩ Z x ∈ B.S.lvlPart B.r P ψ := by
      have := ((range_cv B ⟨X, P, ψ⟩ Z _).1 ⟨x, rfl⟩).2
      rw [hlvl, Submodule.mem_inf] at this
      exact this.2
    exact B.S.lvlIdem_mulVec_of_mem B.r P ψ _ hx
  · rintro ⟨y, rfl⟩
    obtain ⟨hZ, -⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨Ep.mulVec y, rfl⟩
    have hV : cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) ∈ LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin := by
      rw [hlvl, hE, Submodule.mem_inf]
      obtain ⟨-, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨y, rfl⟩
      rw [range_vE_bot] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨⟨(B.S.gaMat B.r (lvlIdem P ψ)).mulVec u, ?_⟩, ?_⟩
      · simp only [Matrix.mulVecLin_apply] at hu ⊢
        rw [← hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, comm_idem B X hX]
      · rw [← level_part_spec K B.S G B.r P ψ]
        exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := (range_cv B ⟨X, P, ψ⟩ Z _).2 ⟨hZ, hV⟩
    exact ⟨x, hinj (by rw [hJ, hx])⟩

end Block2

end PassRep

namespace In

end In

end Formalism.IndefR.CxPass
