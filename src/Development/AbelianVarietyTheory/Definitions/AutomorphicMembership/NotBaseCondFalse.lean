import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj

noncomputable section

namespace GlobalTheory.Mem.Top.GroupRetwisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

abbrev BaseP : Type 1 := ∀ B : Base, Fr B.toPre → Prop

structure BaseCond (KP : BaseP) : Prop where
  ex : EvG fun K => ∃ (P : Pre) (f₀ : Fr P), K.Over P ∧ ∀ (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = P ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def FromCoreAt (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

def Forced (K : Ctx) (B : Base) (T : TwDat B) : Prop :=
  ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl

abbrev AtP : Type 1 := ∀ (_ : Ctx) (B : Base), Fr B.toPre → TwDat B → Prop

def Step (KP : BaseP) (p q : AtP) : Prop := EvLgG fun K B f T => KP B f → Forced K B T → p K B f T → q K B f T

def HasCore (Q : V4.Slot) : AtP := fun K B f T =>
  ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def FirstG (KP : BaseP) (Q : V4.Slot) : Prop := Step KP (fun _ B _ T => T = TwDat.untw B T.pl) (HasCore Q)

def ExportF (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd

def Pass (KP : BaseP) (Q : V4.Slot) (r : AtP) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ r K B' f' T'

def SecondG (KP : BaseP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q (HasCore fun K X f T c => Q K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧ Q' K X f T c)

def LargeBaseConditionG (KP : BaseP) (Q R : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem evG_all {p : Ctx → Prop} (h : ∀ K, p K) : EvG p := evG_good.imp fun K _ _ _ _ _ => h K

theorem baseCond_of {KP : BaseP} (h : V4.KsCond KP) {PP : ∀ P : Pre, Fr P → Prop}
    (hP : EvG fun K => ∃ (P : Pre) (f : Fr P), K.Over P ∧ PP P f) : BaseCond fun B f => KP B f ∧ PP B.toPre f := by
  refine ⟨((evG_of_ev h.ex).inter hP).imp ?_, fun B B' f f' e hf hk => ⟨h.enl B B' f f' e hf hk.1, ?_⟩⟩
  · rintro K _ _ _ _ ⟨hk, P, f₀, hO, hp⟩
    obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
    refine ⟨_, f₀, hO, fun S₁ S₂ a₁ a₂ => ?_⟩
    obtain ⟨B, f, e, hf, k, H⟩ := hk B₀ f₀ S₁ S₂ hO a₁ a₂
    refine ⟨B, f, e, hf, ⟨k, ?_⟩, H⟩
    generalize B₀.toPre = P₀ at *
    subst e
    cases hf
    exact hp
  · have e1 := e.1
    have h2 := hk.2
    clear hk e
    generalize B.toPre = P at *
    generalize B'.toPre = P' at *
    subst e1
    cases hf
    exact h2

theorem lg_forced (K : Ctx) : large₂ K fun B _ T => Forced K B T := by
  have h : ∀ P : Pre, ∃ S : Finset ℕ,
      ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := fun P => by
    refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
    rintro p - (⟨i, rfl⟩ | rfl | h)
    · fin_cases i <;> simp
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))
  choose S hS using h
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem lg_all (K : Ctx) {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, K.Over B.toPre → p B f T) : large₂ K p :=
  (lg_forced K).imp fun B f T hO _ => h B f T hO

section Steps
variable {KP : BaseP} {p q r : AtP}

theorem Step.of_evG (h : EvG fun K => ∀ B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K H

theorem Step.of_all (h : ∀ K B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  Step.of_evG (evG_all h)

theorem Step.trans (h : Step KP p q) (h' : Step KP q r) : Step KP p r :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => G.2 a b (G.1 a b c)

theorem Step.and (h : Step KP p q) (h' : Step KP p r) : Step KP p fun K B f T => q K B f T ∧ r K B f T :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => ⟨G.1 a b c, G.2 a b c⟩

theorem Step.of_evLgG (h : EvLgG q) : Step KP p q := EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G _ _ _ => G

end Steps

end GlobalTheory.Mem.Top.GroupRetwisting

end
