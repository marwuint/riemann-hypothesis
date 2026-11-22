import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

@[nolint unusedArguments] def Idl (_hI : I ^ 2 = 0) (_hs : Function.Surjective π) (_hk : RingHom.ker π = I) : Type := I

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

instance : AddCommGroup (Idl hI hs hk) := inferInstanceAs (AddCommGroup I)
instance : Module R (Idl hI hs hk) := inferInstanceAs (Module R I)
instance : SMul R₀ (Idl hI hs hk) := ⟨fun r x ↦ Function.surjInv hs r • x⟩

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

theorem smul_idl (r : R) (x : Idl hI hs hk) : π r • x = r • x := by
  change Function.surjInv hs (π r) • x = r • x
  rw [← sub_eq_zero, ← sub_smul]
  refine Subtype.ext (mul_eq_zero_of_mem hI ?_ x.2)
  rw [← hk, RingHom.mem_ker, map_sub, Function.surjInv_eq hs, sub_self]

instance : Module R₀ (Idl hI hs hk) := hs.moduleLeft π (smul_idl hI hs hk)
instance : Module R₀ᵐᵒᵖ (Idl hI hs hk) := Module.compHom _ ((RingHom.id R₀).fromOpposite mul_comm)
instance : IsCentralScalar R₀ (Idl hI hs hk) := ⟨fun _ _ ↦ rfl⟩

def aug : Aug I π (TrivSqZeroExt R₀ (Idl hI hs hk)) where
  q := TrivSqZeroExt.fstHom R₀ R₀ _
  k := { toFun := fun y ↦ (show I from y.snd).1, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  mem y := (show I from y.snd).2
  smul r y := congrArg Subtype.val (smul_idl hI hs hk r y.snd)
  one := rfl
  sq y y' h h' := by
    have h1 : y.fst = 0 := h
    have h2 : y'.fst = 0 := h'
    ext <;> simp [h1, h2]
  inj y h h' := TrivSqZeroExt.ext h (Subtype.ext h')
  surj i hi := ⟨TrivSqZeroExt.inr (show Idl hI hs hk from ⟨i, hi⟩), rfl, rfl⟩

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

include hI hs in

theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add, e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

def sec (α : Aug I π R₁) : I →+ R₁ := AddMonoidHom.mk' (fun i ↦ (α.surj i.1 i.2).choose) fun i j ↦ by
  have h := fun i : I ↦ (α.surj i.1 i.2).choose_spec
  rw [← sub_eq_zero]
  exact α.inj _ (by simp only [map_sub, map_add, (h _).1]; ring) (by simp only [map_sub, map_add, (h _).2]; simp)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

abbrev sh (i : I) : R[X] →ₐ[R] R[X] := aeval (X + C (i : R))

variable {C : Type} [Category.{0} C]

def th (α : Aug I π R₁) (σ : R₁ ⊗[R₀] R₀[X] →+ R[X]) (i : I) : Ω[R₀[X]⁄R₀] →+ R[X] :=
  AddMonoidHom.mk' (fun w ↦ σ (sec α i ⊗ₜ polynomialEquiv R₀ w)) fun _ _ ↦ by
    rw [map_add, TensorProduct.tmul_add, map_add]

end Line

end GlobalTheory.Obs.Model
