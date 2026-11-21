import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

end Defs

end GlobalTheory.TorRef
