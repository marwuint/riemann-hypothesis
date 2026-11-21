import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.HermitianForms.BothLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

variable (T : CF.TilTied u A K (P D.R.m le_rfl))

end Formalism.L2.Col
