import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

def MarkedBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (h γ : 𝔾) : Prop :=
  γ ∈ Γ ∧
    ((U.X (dict h).1).Λ : Set (Fin r → E)) =
      (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)

variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)

variable (Xo) in

def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

end GlobalTheory.XiDetCompare
