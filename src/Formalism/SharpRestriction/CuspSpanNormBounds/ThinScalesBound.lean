import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.ParConsts

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound

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
