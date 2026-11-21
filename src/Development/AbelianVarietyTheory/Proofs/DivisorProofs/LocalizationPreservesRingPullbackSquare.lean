import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMkOfComp

namespace GlobalTheory

theorem locPullback : ∀ {A R₀ A' B₀ : Type} [CommRing A] [CommRing R₀] [CommRing A'] [CommRing B₀]
    (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), α.comp φ = κ.comp ψ →
    (∀ a, φ a = 0 → ψ a = 0 → a = 0) → (∀ r c, α r = κ c → ∃ a, φ a = r ∧ ψ a = c) →
    ∀ (s : A) (LA LR LA' LB : Type) [CommRing LA] [CommRing LR] [CommRing LA'] [CommRing LB]
    [Algebra A LA] [Algebra R₀ LR] [Algebra A' LA'] [Algebra B₀ LB]
    [IsLocalization.Away s LA] [IsLocalization.Away (φ s) LR] [IsLocalization.Away (ψ s) LA']
    [IsLocalization.Away (α (φ s)) LB]
    (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB),
    Φ.comp (algebraMap A LA) = (algebraMap R₀ LR).comp φ →
    Ψ.comp (algebraMap A LA) = (algebraMap A' LA').comp ψ →
    Aα.comp (algebraMap R₀ LR) = (algebraMap B₀ LB).comp α →
    Kκ.comp (algebraMap A' LA') = (algebraMap B₀ LB).comp κ →
    (∀ t, Φ t = 0 → Ψ t = 0 → t = 0) ∧ ∀ a b, Aα a = Kκ b → ∃ t, Φ t = a ∧ Ψ t = b := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.QuotientMapComposition.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.QuotientMapComposition.main
  | exact @_root_.GlobalTheory.QuotientMapComposition.main
  | exact _root_.GlobalTheory.QuotientMapComposition.main
  | (apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMapComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMapComposition.main ..)

end GlobalTheory
