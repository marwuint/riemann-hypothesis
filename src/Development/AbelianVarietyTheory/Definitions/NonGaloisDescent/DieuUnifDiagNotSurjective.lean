import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

noncomputable section

open CategoryTheory Module Matrix

namespace GlobalTheory.VDiv

section Modules

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (S : Type) [CommRing S] [Algebra O S]

structure VarpiDivModule : Type 1 where

  G : PDivGroup p S

  ι : PDivGroup.Action O G

  isNilpotent_p : IsNilpotent (p : S)

  lie_smul : ∀ (a : O) (x : G.Lie), ι.onLie a x = algebraMap O S a • x

namespace VarpiDivModule

variable {p O S}

@[ext] structure Hom (H H' : VarpiDivModule p O S) : Type where

  f : H.G ⟶ H'.G

  comm : ∀ a : O, (H.ι a : H.G ⟶ H.G) ≫ f = f ≫ (H'.ι a : H'.G ⟶ H'.G)

instance : Category (VarpiDivModule p O S) where
  Hom := Hom
  id H := ⟨𝟙 _, fun a => by rw [Category.comp_id, Category.id_comp]⟩
  comp f g := ⟨f.f ≫ g.f, fun a => by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp f.f)
  comp_id f := Hom.ext (Category.comp_id f.f)
  assoc f g h := Hom.ext (Category.assoc f.f g.f h.f)

@[simp] theorem id_f (H : VarpiDivModule p O S) : Hom.f (𝟙 H) = 𝟙 H.G := rfl

@[simp] theorem comp_f {H H' H'' : VarpiDivModule p O S} (f : H ⟶ H') (g : H' ⟶ H'') :
    Hom.f (f ≫ g) = f.f ≫ g.f := rfl

theorem padicAction_onLie [Algebra ℤ_[p] S] (G : PDivGroup p S) (a : ℤ_[p]) (x : G.Lie) :
    (PDivGroup.padicAction G).onLie a x = algebraMap ℤ_[p] S a • x := by
  rw [PDivGroup.Action.onLie_apply, PDivGroup.padicAction, Algebra.algebraMap_eq_smul_one,
    PDivGroup.lieMap_smul (algebraMap ℤ_[p] S)]
  simp

variable (p) in

def ofPDiv [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    VarpiDivModule p ℤ_[p] S :=
  ⟨G, G.padicAction, h, padicAction_onLie G⟩

@[simp] theorem ofPDiv_G [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    (ofPDiv p G h).G = G := rfl

variable (p) in

abbrev ResRing : Type := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}

theorem natCast_resRing : ((p : ℕ) : ResRing p) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}))]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable (p) in

def muMod : VarpiDivModule p ℤ_[p] (ResRing p) :=
  ofPDiv p (PDivGroup.mu p (ResRing p)) ⟨1, by rw [pow_one, natCast_resRing]⟩

end VarpiDivModule

end Modules

section Bset

variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]

def unifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update 1 0 ϖ)

def coUnifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update (fun _ => ϖ) 0 1)

theorem unifDiag_mul_coUnifDiag (ϖ : R) :
    (unifDiag ϖ : Matrix (Fin n) (Fin n) R) * coUnifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

theorem coUnifDiag_mul_unifDiag (ϖ : R) :
    (coUnifDiag ϖ : Matrix (Fin n) (Fin n) R) * unifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

variable (n) in

def BsetInt (ϖ : R) : Set (Matrix (Fin n) (Fin n) R) :=
  {β | ∃ k₁ k₂ : GL (Fin n) R, β = k₁.val * unifDiag ϖ * k₂.val}

theorem exists_mul_eq_smul {ϖ : R} {β : Matrix (Fin n) (Fin n) R} (hβ : β ∈ BsetInt n ϖ) :
    ∃ γ : Matrix (Fin n) (Fin n) R, β * γ = ϖ • 1 ∧ γ * β = ϖ • 1 := by
  obtain ⟨k₁, k₂, rfl⟩ := hβ
  refine ⟨(k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val, ?_, ?_⟩
  · calc k₁.val * unifDiag ϖ * k₂.val * ((k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val)
        = k₁.val * (unifDiag ϖ * ((k₂.val * (k₂⁻¹).val) * coUnifDiag ϖ)) * (k₁⁻¹).val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
            unifDiag_mul_coUnifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · calc (k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val * (k₁.val * unifDiag ϖ * k₂.val)
        = (k₂⁻¹).val * (coUnifDiag ϖ * (((k₁⁻¹).val * k₁.val) * unifDiag ϖ)) * k₂.val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
            coUnifDiag_mul_unifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, inv_mul_cancel, Units.val_one]

def sigmaGL (σ : R ≃+* R) : GL (Fin n) R →* GL (Fin n) R :=
  GeneralLinearGroup.map (σ : R →+* R)

@[simp] theorem sigmaGL_val (σ : R ≃+* R) (g : GL (Fin n) R) :
    (sigmaGL σ g).val = (g.val).map σ := rfl

def sigmaConj (σ : R ≃+* R) (g : GL (Fin n) R) (β : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  g.val * β * (sigmaGL σ g⁻¹).val

@[simp] theorem sigmaConj_one (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    sigmaConj σ 1 β = β := by
  simp only [sigmaConj, inv_one, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

end Bset

section Dieudonne

variable (R : Type) [CommRing R]

structure RelDieudonne (σ : R ≃+* R) (ϖ : R) : Type 1 where

  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [free : Module.Free R M]
  [finite : Module.Finite R M]

  F : M →ₛₗ[(σ : R →+* R)] M

  V : M →ₛₗ[(σ.symm : R →+* R)] M

  F_V : ∀ x, F (V x) = ϖ • x

  V_F : ∀ x, V (F x) = ϖ • x

attribute [instance] RelDieudonne.addCommGroup RelDieudonne.module RelDieudonne.free
  RelDieudonne.finite

variable {R}

namespace RelDieudonne

variable {σ : R ≃+* R} {ϖ : R}

structure Iso (D D' : RelDieudonne R σ ϖ) : Type where

  e : D.M ≃ₗ[R] D'.M

  F_comm : ∀ x, e (D.F x) = D'.F (e x)

  V_comm : ∀ x, e (D.V x) = D'.V (e x)

def Iso.refl (D : RelDieudonne R σ ϖ) : Iso D D :=
  ⟨LinearEquiv.refl R D.M, fun _ => rfl, fun _ => rfl⟩

def Iso.symm {D D' : RelDieudonne R σ ϖ} (i : Iso D D') : Iso D' D :=
  ⟨i.e.symm, fun x => i.e.injective (by rw [i.F_comm, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]), fun x => i.e.injective (by rw [i.V_comm,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])⟩

def Iso.trans {D D' D'' : RelDieudonne R σ ϖ} (i : Iso D D') (j : Iso D' D'') : Iso D D'' :=
  ⟨i.e.trans j.e, fun x => by simp [i.F_comm, j.F_comm], fun x => by simp [i.V_comm, j.V_comm]⟩

end RelDieudonne

variable {n : ℕ}

def dieuF (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ : R →+* R)] (Fin n → R) where
  toFun x := β *ᵥ fun i => σ (x i)
  map_add' x y := by
    rw [← mulVec_add]
    congr 1
    funext i
    simp
  map_smul' c x := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp

def dieuV (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ.symm : R →+* R)] (Fin n → R) where
  toFun y i := σ.symm ((γ *ᵥ y) i)
  map_add' x y := by
    funext i
    simp [mulVec_add]
  map_smul' c x := by
    funext i
    simp [mulVec_smul]

@[simp] theorem dieuF_apply (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    dieuF σ β x = β *ᵥ fun i => σ (x i) := rfl

@[simp] theorem dieuV_apply (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) (y : Fin n → R)
    (i : Fin n) : dieuV σ γ y i = σ.symm ((γ *ᵥ y) i) := rfl

variable [NeZero n]

def coMat {ϖ : R} (β : BsetInt n ϖ) : Matrix (Fin n) (Fin n) R :=
  (exists_mul_eq_smul β.2).choose

theorem mul_coMat {ϖ : R} (β : BsetInt n ϖ) : β.1 * coMat β = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.1

theorem coMat_mul {ϖ : R} (β : BsetInt n ϖ) : coMat β * β.1 = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.2

def dieu (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ) : RelDieudonne R σ ϖ where
  M := Fin n → R
  F := dieuF σ β.1
  V := dieuV σ (coMat β)
  F_V y := by
    have h1 : (fun i => σ (dieuV σ (coMat β) y i)) = coMat β *ᵥ y := by
      funext i; rw [dieuV_apply, RingEquiv.apply_symm_apply]
    rw [dieuF_apply, h1, mulVec_mulVec, mul_coMat, smul_mulVec, one_mulVec]
  V_F x := by
    funext i
    rw [dieuV_apply, dieuF_apply, mulVec_mulVec, coMat_mul, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    rw [show σ.symm ϖ = ϖ from σ.symm_apply_eq.2 hϖ.symm]

@[simp] theorem dieu_F (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ)
    (x : Fin n → R) : (dieu σ hϖ β).F x = β.1 *ᵥ fun i => σ (x i) := rfl

end Dieudonne

section Conj

variable {R : Type} [CommRing R] {σ : R ≃+* R} {ϖ : R}

variable {n : ℕ}

def glEquiv (g : GL (Fin n) R) : (Fin n → R) ≃ₗ[R] (Fin n → R) where
  toFun x := g.val *ᵥ x
  invFun y := (g⁻¹).val *ᵥ y
  map_add' x y := mulVec_add _ _ _
  map_smul' c x := mulVec_smul _ _ _
  left_inv x := by
    change (g⁻¹).val *ᵥ (g.val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv y := by
    change g.val *ᵥ ((g⁻¹).val *ᵥ y) = y
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

@[simp] theorem glEquiv_apply (g : GL (Fin n) R) (x : Fin n → R) : glEquiv g x = g.val *ᵥ x := rfl

variable [NeZero n]

end Conj

end GlobalTheory.VDiv
