import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.ParConsts

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound

open scoped Classical in

def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      M.Ns s t t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * M.N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = M.Ns s t t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * M.N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, M.N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * M.N0 (h a) (h b) -
      Th x a b).PosSemidef)

def FamilyTheoremThreePassage {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ H.NGrp t.abelian₂ t.f, ∀ nn' ∈ H.NGrp t.abelian₂ t.f',
    (∀ x ∈ t.abelian₂, nn x - nn' x ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂) →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a b, uL a b ∈ M.R ∧ uU a b ∈ M.R) ∧
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU

def FrameK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (T : F) : Prop :=
  (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T

def FamilyLocalModel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r), H.IsGeneric t₁ →
  ∀ (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'),
    FrameK H f₂ t₁.T → FrameK H f₂' t₁.T' →
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' →
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) →
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)) →
  let S : Set (Submodule M.L.O V) := {Λ₂ | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
    H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'}
  let P₁ := H.ZZplus t₁
  let P₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  (H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = P₁ → Z₂.Z.map M.R.subtype = P₂ →
      Nat.card S = M.nIso Z₁ Z₂) ∧
  (IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = P₁ a.castSucc (Fin.last r) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last r) ∧
        (al₁ a : E) = P₁ (Fin.last r) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last r) a.castSucc) →
      Nat.card S = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂)

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def T2 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => FamilyLocalModel M D.R.rS D.R.r)

end Formalism.MainNotions.ThinScalesBound

end
