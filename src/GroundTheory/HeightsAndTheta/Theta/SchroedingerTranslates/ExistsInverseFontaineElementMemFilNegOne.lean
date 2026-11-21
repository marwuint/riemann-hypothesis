import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
import GroundTheory.HeightsAndTheta.Theta.GaussianExample
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

namespace GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys

open GroundTheory.Automorphic GroundTheory.Heights₂.Theta MeasureTheory TensorProduct NumberField
open scoped NNReal ENNReal SchwartzMap NumberField.AdeleRing

noncomputable section

section SystemL

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (A : Type*) [AddCommGroup A] [Module E A]

structure HermL where

  form : A →ₗ[E] A →ₛₗ[conjHom F E] E

  herm : ∀ x y, form y x = conj F E (form x y)

  nonsingular : Function.Bijective form

variable {F E A}

namespace HermL

def unitaryGroup (h : HermL F E A) : Subgroup (A ≃ₗ[E] A) where
  carrier := {g | ∀ x y, h.form (g x) (g y) = h.form x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb x y := by
    change h.form (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    change h.form (a.symm x) (a.symm y) = _
    conv_rhs => rw [← a.apply_symm_apply x, ← a.apply_symm_apply y]
    rw [ha]

theorem mem_unitaryGroup {h : HermL F E A} {g : A ≃ₗ[E] A} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.form (g x) (g y) = h.form x y := Iff.rfl

end HermL

end SystemL

section Tensor

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {A B : Type*} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]

def tensorHermitianPartial (hA : HermL F E A) (hB : HermL F E B) (a : A) (b : B) :
    A →ₛₗ[conjHom F E] B →ₛₗ[conjHom F E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (conjHom F E) (fun a' b' => hA.form a a' * hB.form b b')
    (fun _ _ _ => by rw [map_add, add_mul])
    (fun _ _ _ => by rw [LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun _ _ _ => by rw [map_add, mul_add])
    (fun _ _ _ => by rw [LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, mul_left_comm])

def tensHerm (hA : HermL F E A) (hB : HermL F E B) :
    A ⊗[E] B →ₗ[E] A ⊗[E] B →ₛₗ[conjHom F E] E :=
  TensorProduct.lift (LinearMap.mk₂ E (fun a b => TensorProduct.lift (tensorHermitianPartial hA hB a b))
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.add_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_add, LinearMap.add_apply, add_mul])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.smul_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_smul, smul_eq_mul, mul_assoc])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.add_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_add, LinearMap.add_apply, mul_add])
    (fun _ _ _ => TensorProduct.ext' fun _ _ => by
      simp only [TensorProduct.lift.tmul, LinearMap.smul_apply, tensorHermitianPartial,
        LinearMap.mk₂'ₛₗ_apply, map_smul, smul_eq_mul]
      ring))

@[simp] theorem tensHerm_tmul (hA : HermL F E A) (hB : HermL F E B) (a a' : A) (b b' : B) :
    tensHerm hA hB (a ⊗ₜ b) (a' ⊗ₜ b') = hA.form a a' * hB.form b b' := by
  simp only [tensHerm, TensorProduct.lift.tmul, LinearMap.mk₂_apply, tensorHermitianPartial,
    LinearMap.mk₂'ₛₗ_apply]

variable [Module F A] [IsScalarTower F E A]

def weilForm (ξ : E) (hA : HermL F E A) (hB : HermL F E B) : LinearMap.BilinForm F (A ⊗[E] B) :=
  LinearMap.mk₂ F (fun w w' => Algebra.trace F E (ξ * tensHerm hA hB w w'))
    (fun _ _ _ => by rw [map_add, LinearMap.add_apply, mul_add, map_add])
    (fun c w w' => by
      rw [← algebraMap_smul E c w, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_left_comm,
        ← Algebra.smul_def, map_smul, smul_eq_mul])
    (fun _ _ _ => by rw [map_add, mul_add, map_add])
    (fun c w w' => by
      rw [← algebraMap_smul E c w', LinearMap.map_smulₛₗ, smul_eq_mul]
      change Algebra.trace F E (ξ * (conj F E (algebraMap F E c) * _)) = _
      rw [conj_algebraMap, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul])

theorem weilForm_apply (ξ : E) (hA : HermL F E A) (hB : HermL F E B) (w w' : A ⊗[E] B) :
    weilForm ξ hA hB w w' = Algebra.trace F E (ξ * tensHerm hA hB w w') := rfl

end Tensor

section Heisenberg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def Sp (ω : LinearMap.BilinForm R W) : Subgroup (W ≃ₗ[R] W) where
  carrier := {g | ∀ w w', ω (g w) (g w') = ω w w'}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb w w' := by
    change ω (a (b w)) (a (b w')) = _
    rw [ha, hb]
  inv_mem' {a} ha w w' := by
    change ω (a.symm w) (a.symm w') = _
    conv_rhs => rw [← a.apply_symm_apply w, ← a.apply_symm_apply w']
    rw [ha]

theorem mem_Sp {ω : LinearMap.BilinForm R W} {g : W ≃ₗ[R] W} :
    g ∈ Sp ω ↔ ∀ w w', ω (g w) (g w') = ω w w' := Iff.rfl

@[ext]
structure Heis (ω : LinearMap.BilinForm R W) where

  w : W

  t : R

variable {ω : LinearMap.BilinForm R W}

instance : One (Heis ω) := ⟨⟨0, 0⟩⟩

@[simp] theorem Heis.one_w : (1 : Heis ω).w = 0 := rfl

@[simp] theorem Heis.indicator_eq_one_of_true : (1 : Heis ω).t = 0 := rfl

variable [Invertible (2 : R)]

instance : Mul (Heis ω) := ⟨fun h h' => ⟨h.w + h'.w, h.t + h'.t + ⅟2 * ω h.w h'.w⟩⟩

instance : Inv (Heis ω) := ⟨fun h => ⟨-h.w, -h.t + ⅟2 * ω h.w h.w⟩⟩

@[simp] theorem Heis.mul_w (h h' : Heis ω) : (h * h').w = h.w + h'.w := rfl

@[simp] theorem Heis.product_torus_component (h h' : Heis ω) : (h * h').t = h.t + h'.t + ⅟2 * ω h.w h'.w := rfl

@[simp] theorem Heis.inv_w (h : Heis ω) : h⁻¹.w = -h.w := rfl

@[simp] theorem Heis.exists_inverse_fontaineElement_mem_fil_neg_one (h : Heis ω) : h⁻¹.t = -h.t + ⅟2 * ω h.w h.w := rfl

instance : Group (Heis ω) :=
  Group.ofLeftAxioms
    (fun a b c => by
      ext
      · simp [add_assoc]
      · simp only [Heis.product_torus_component, Heis.mul_w, map_add, LinearMap.add_apply]
        ring)
    (fun a => by ext <;> simp)
    (fun a => by
      ext
      · simp
      · simp only [Heis.product_torus_component, Heis.exists_inverse_fontaineElement_mem_fil_neg_one, Heis.inv_w, Heis.indicator_eq_one_of_true, map_neg, LinearMap.neg_apply]
        ring)

structure Polarization (ω : LinearMap.BilinForm R W) (X Y : Type*) [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] where

  e : (X × Y) ≃ₗ[R] W

  isotropic_X : ∀ x x' : X, ω (e (x, 0)) (e (x', 0)) = 0

  isotropic_Y : ∀ y y' : Y, ω (e (0, y)) (e (0, y')) = 0

namespace Polarization

end Polarization

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

end Heisenberg

section Examples

def gaussFormL : GaussQ →ₗ[GaussQ] GaussQ →ₛₗ[conjHom ℚ GaussQ] GaussQ :=
  LinearMap.mk₂'ₛₗ (RingHom.id GaussQ) (conjHom ℚ GaussQ) (fun x y => x * conj ℚ GaussQ y)
    (fun _ _ _ => add_mul _ _ _)
    (fun c x y => by rw [smul_eq_mul, smul_eq_mul, RingHom.id_apply, mul_assoc])
    (fun x y y' => by rw [map_add, mul_add])
    (fun c x y => by
      show x * conj ℚ GaussQ (c * y) = conj ℚ GaussQ c * (x * conj ℚ GaussQ y)
      rw [map_mul]
      ring)

theorem gaussFormL_apply (x y : GaussQ) : gaussFormL x y = x * conj ℚ GaussQ y := rfl

def stdSymp (R : Type*) [CommRing R] : LinearMap.BilinForm R (R × R) :=
  LinearMap.mk₂ R (fun u v => u.1 * v.2 - u.2 * v.1)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem stdSymp_apply (R : Type*) [CommRing R] (u v : R × R) :
    stdSymp R u v = u.1 * v.2 - u.2 * v.1 := rfl

end Examples

end

end GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys
