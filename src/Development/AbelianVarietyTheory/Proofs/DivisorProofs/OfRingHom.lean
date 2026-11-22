import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.BdDim

section Fibres

variable {T X Y Z : Scheme.{0}}

def SameFibre (G : Over X) [GrpObj G] (x : T ⟶ X) (G' : Over Y) [GrpObj G'] (y : T ⟶ Y) : Prop :=
  ∃ (A : Over T) (_ : GrpObj A) (φ : A.left ⟶ G.left) (ψ : A.left ⟶ G'.left),
    IsGrpPullback A G x φ ∧ IsGrpPullback A G' y ψ

def IsAbPart {k : Type} [Field k] (G : Over X) [GrpObj G] (x : Sp k ⟶ X) (B : Over Y) [GrpObj B] (y : Sp k ⟶ Y) : Prop :=
  ∃ (A : Over (Sp k)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (t : TorusExtension A) (β : t.B.left ⟶ B.left),
    IsGrpPullback A G x φ ∧ @IsGrpPullback _ _ t.B t.grpB B _ y β

theorem IsAbPart.trans {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {B' : Over Z} [GrpObj B'] {z : Sp k ⟶ Z} (h : IsAbPart G x B y) (h' : SameFibre B y B' z) : IsAbPart G x B' z := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  obtain ⟨C, _, ψ, ψ', h₃, h₄⟩ := h'
  letI := t.grpB
  obtain ⟨e, he, -⟩ := grpPullback_iso h₂ h₃
  exact ⟨A, _, φ, t, _, h₁, ((isGrpPullback_of_iso e).comp h₄).congr (Category.id_comp _) rfl⟩

theorem IsAbPart.comp {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {G' : Over Z} [GrpObj G'] {f : X ⟶ Z} {φ : G.left ⟶ G'.left} (h : IsAbPart G x B y) (h' : IsGrpPullback G G' f φ) :
    IsAbPart G' (x ≫ f) B y := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  exact ⟨A, _, _, t, β, h₁.comp h', h₂⟩

end Fibres

end GlobalTheory.BdDim

end
