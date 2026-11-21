import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.S.TieN

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SameFrameClass (D : D7) (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (F' F'₂ : LFlag (hS D) D.R.rS T') : Prop :=
  ∃ n ∈ NLam Λ F, ∃ m ∈ NLam Λ F', ∀ b, frame F'₂ b = n (m (frame F' b))

def TermInj (D : D7) (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u', X.abelian₂ t = X.abelian₂ t' → SameFrameClass D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

section Mass

open Formalism.MainNotions.S.LocalSplitGroups

def MassDef (D : D7) (X : TermTie D) (Z : TermLocs D X) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p)
    (u u' : D.what₂.Word),
    ∃ (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
      (Z δ M hA u u').massTot = ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D F0 Λ ∧
      ∀ γ, (Z δ M hA u u').massT γ = Formalism.MainNotions.S.wRow D F0 (X.abelian₂ γ) / (Z δ M hA u u').massTot

end Mass

section Cnt

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def CntMassOK (Z : TermLoc D X δ M u u') (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ Z.massTot = ∑ Λ ∈ what₂, wRow D F0 Λ ∧
    ∀ γ, Z.massT γ = wRow D F0 (X.abelian₂ γ) / Z.massTot

def IntLow {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ Mp.R

def IntUp {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (ρ : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ Mp.R

theorem massDef_iff (D : D7) (X : TermTie D) (Z : TermLocs D X) :
    MassDef D X Z ↔ ∀ δ M hA u u', ∃ F0 what₂, CntMassOK (Z δ M hA u u') F0 what₂ := Iff.rfl

end Cnt

end Formalism.MainNotions.S.TieN
