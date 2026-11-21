import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.ChainComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped NumberField TensorProduct
open GlobalTheory.Cris DividedPowers
attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory.SSG

structure DRChain (C : Type) [CommRing C] (n : ℕ) : Type (u + 1) where

  M : Fin (n + 1) → Type u
  [acg : ∀ i, AddCommGroup (M i)]
  [mod : ∀ i, Module C (M i)]

  f : ∀ i : Fin n, M i.castSucc →ₗ[C] M i.succ

  g : M (Fin.last n) →ₗ[C] M 0

  ω : ∀ i, Submodule C (M i)

attribute [instance] DRChain.acg DRChain.mod

namespace DRChain

variable {C : Type} [CommRing C] {n : ℕ}

def comp (X : DRChain.{u} C n) : ∀ i : Fin (n + 1), X.M 0 →ₗ[C] X.M i :=
  Fin.induction LinearMap.id (fun i h ↦ X.f i ∘ₗ h)

@[simp] theorem comp_zero (X : DRChain.{u} C n) : X.comp 0 = LinearMap.id := rfl

@[simp] theorem comp_succ (X : DRChain.{u} C n) (i : Fin n) :
    X.comp i.succ = X.f i ∘ₗ X.comp i.castSucc := rfl

theorem comp_eq_chainComp (X : DRChain.{0} C n) : X.comp = chainComp X.f := rfl

end DRChain

end GlobalTheory.SSG

namespace GlobalTheory.DeRham

variable {C : Type} [CommRing C] {O : Type} [Ring O]
  {B B' B'' : Over (Sp C)} [GrpObj B] [GrpObj B'] [GrpObj B'']

theorem primPull_comp (f : B ⟶ B') (g : B' ⟶ B'') [IsMonHom f] [IsMonHom g] :
    primPull (dp0 C) (𝟙 _) (f ≫ g) = primPull (dp0 C) (𝟙 _) f ∘ₗ primPull (dp0 C) (𝟙 _) g :=
  LinearMap.ext fun c ↦ (GrpMor.pull_pull (homMor (dp0 C) (𝟙 _) g) (homMor (dp0 C) (𝟙 _) f)
    (homMor (dp0 C) (𝟙 _) (f ≫ g)) (fun _ ↦ rfl) rfl c).symm

theorem primPull_congr {f g : B ⟶ B'} [IsMonHom f] [IsMonHom g] (e : f = g) :
    primPull (dp0 C) (𝟙 _) f = primPull (dp0 C) (𝟙 _) g := by
  subst e; rfl

theorem primPull_mul (f g : B ⟶ B') [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    primPull (dp0 C) (𝟙 _) (f * g) = primPull (dp0 C) (𝟙 _) f + primPull (dp0 C) (𝟙 _) g :=
  LinearMap.ext fun c ↦ Subtype.ext (c.2 B f g)

variable [IsCommMonObj B] [IsCommMonObj B'] [IsCommMonObj B'']

def opPull (ρ : RingAct B O) (x : O) : Module.End C (primDR B) :=
  haveI := ρ.hom x
  primPull (dp0 C) (𝟙 _) (ρ.act x)

theorem opPull_add (ρ : RingAct B O) (x y : O) : opPull ρ (x + y) = opPull ρ x + opPull ρ y := by
  haveI := ρ.hom
  have e : ρ.act (x + y) = ρ.act x * ρ.act y := ρ.map_add x y
  haveI : IsMonHom (ρ.act x * ρ.act y) := e ▸ ρ.hom _
  exact (primPull_congr e).trans (primPull_mul _ _)

def opPullHom (ρ : RingAct B O) : O →+ Module.End C (primDR B) :=
  AddMonoidHom.mk' (opPull ρ) (opPull_add ρ)

def tensorPull (ρ : RingAct B O) : C ⊗[ℤ] O →ₗ[ℤ] Module.End C (primDR B) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (c : C) (x : O) ↦ c • opPull ρ x)
    (fun c c' x ↦ add_smul c c' _)
    (fun k c x ↦ smul_assoc k c _)
    (fun c x y ↦ by rw [opPull_add, smul_add])
    (fun k c x ↦ by
      change c • opPullHom ρ (k • x) = k • (c • opPullHom ρ x)
      rw [map_zsmul, smul_comm]))

@[simp] theorem tensorPull_tmul (ρ : RingAct B O) (c : C) (x : O) :
    tensorPull ρ (c ⊗ₜ x) = c • opPull ρ x := rfl

def eigSub (ρ : RingAct B O) {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C) :
    Submodule C (primDR B) :=
  ⨅ x : K, LinearMap.ker (opPull ρ (algebraMap K O x) - χ x • (1 : Module.End C (primDR B)))

theorem mem_eigSub {ρ : RingAct B O} {K : Type} [CommRing K] [Algebra K O] {χ : K →+* C}
    {h : primDR B} : h ∈ eigSub ρ χ ↔ ∀ x, opPull ρ (algebraMap K O x) h = χ x • h := by
  simp [eigSub, Submodule.mem_iInf, sub_eq_zero]

def epsPart (ρ : RingAct B O) {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C) (ε : C ⊗[ℤ] O) :
    Submodule C (primDR B) :=
  eigSub ρ χ ⊓ LinearMap.range (tensorPull ρ ε)

theorem primPull_opPull {ρ : RingAct B O} {ρ' : RingAct B' O} {u : B' ⟶ B}
    (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (x : O) :
    haveI := hu.hom
    primPull (dp0 C) (𝟙 _) u ∘ₗ opPull ρ x = opPull ρ' x ∘ₗ primPull (dp0 C) (𝟙 _) u := by
  haveI := hu.hom
  haveI := ρ.hom
  haveI := ρ'.hom
  unfold opPull
  rw [← primPull_comp, ← primPull_comp]
  exact primPull_congr (hu.comm x).symm

theorem primPull_tensorPull {ρ : RingAct B O} {ρ' : RingAct B' O} {u : B' ⟶ B}
    (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (z : C ⊗[ℤ] O) :
    haveI := hu.hom
    primPull (dp0 C) (𝟙 _) u ∘ₗ tensorPull ρ z = tensorPull ρ' z ∘ₗ primPull (dp0 C) (𝟙 _) u := by
  haveI := hu.hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => rw [tensorPull_tmul, tensorPull_tmul, LinearMap.comp_smul, LinearMap.smul_comp,
      primPull_opPull hu]
  | add z z' hz hz' => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hz, hz']

def pullPart {ρ : RingAct B O} {ρ' : RingAct B' O} {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C)
    (ε : C ⊗[ℤ] O) (u : B' ⟶ B) (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) : epsPart ρ χ ε →ₗ[C] epsPart ρ' χ ε :=
  haveI := hu.hom
  (primPull (dp0 C) (𝟙 _) u).restrict fun h hh ↦ by
    refine ⟨mem_eigSub.2 fun x ↦ ?_, ?_⟩
    · have e := LinearMap.congr_fun (primPull_opPull hu (algebraMap K O x)) h
      simp only [LinearMap.comp_apply] at e
      rw [← e, mem_eigSub.1 hh.1 x, map_smul]
    · obtain ⟨y, hy⟩ := hh.2
      refine ⟨primPull (dp0 C) (𝟙 _) u y, ?_⟩
      rw [← hy]
      exact (LinearMap.congr_fun (primPull_tensorPull hu ε) y).symm

theorem pullPart_apply {ρ : RingAct B O} {ρ' : RingAct B' O} {K : Type} [CommRing K] [Algebra K O]
    (χ : K →+* C) (ε : C ⊗[ℤ] O) (u : B' ⟶ B) (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (h : epsPart ρ χ ε) :
    haveI := hu.hom
    (pullPart χ ε u hu h : primDR B') = primPull (dp0 C) (𝟙 _) u h := rfl

end GlobalTheory.DeRham

namespace GlobalTheory.IwLevel

namespace Chain

variable {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
  {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (X : Chain ρ 𝔴 d n)

def close (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : X.B i ⟶ A :=
  (X.existsUnique_close i ha).exists.choose

theorem π_close (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : X.π i ≫ X.close i ha = ρ.act a :=
  (X.existsUnique_close i ha).exists.choose_spec

instance close_isMonHom (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : IsMonHom (X.close i ha) := by
  have h := X.π_deg i
  have := h.flat
  have := h.surj
  haveI := (X.π_lin i).hom
  haveI := ρ.hom a
  have e := X.π_close i ha
  haveI := GlobalTheory.FlatQuotient.epi_tensorHom (X.π i) (X.π i)
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom (X.π i), Category.assoc, e, IsMonHom.one_hom]
  · rw [← cancel_epi (X.π i ⊗ₘ X.π i)]
    calc (X.π i ⊗ₘ X.π i) ≫ μ ≫ X.close i ha = (μ ≫ X.π i) ≫ X.close i ha := by
          rw [IsMonHom.mul_hom (X.π i), Category.assoc]
      _ = μ ≫ ρ.act a := by rw [Category.assoc, e]
      _ = (ρ.act a ⊗ₘ ρ.act a) ≫ μ := IsMonHom.mul_hom _
      _ = (X.π i ⊗ₘ X.π i) ≫ (X.close i ha ⊗ₘ X.close i ha) ≫ μ := by
          rw [← Category.assoc, tensorHom_comp_tensorHom, e]

end Chain

end GlobalTheory.IwLevel

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT

