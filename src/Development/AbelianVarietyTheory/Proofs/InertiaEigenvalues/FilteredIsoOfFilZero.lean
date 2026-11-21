import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom

noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_mapdR_eq {K LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {T T' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.mapdR P f = _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mapdR (Qp := ℚ_[l]) (BdR := P.R.BdR) f :=
  rfl

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem strictness_of_dualExactSequence_strict
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore
  · intro K s LL hg T₀ T₁ T₂ f g hf hg' hi he hs h₀ h₁ h₂ τ a
    obtain ⟨k₁, k₂, k₃⟩ := h K s LL hg T₀ T₁ T₂ f g ⟨hf, hg', hi, he, hs⟩ h₀ h₁ h₂ τ a
    simp only [dualExactSequence_mapdR_eq] at k₁ k₂ k₃
    refine ⟨k₁, ?_, ?_⟩
    · ext y
      simpa [Submodule.mem_inf] using k₂ y
    · ext z
      simpa using k₃ z

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_strict_of_strictness
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb
  · intro K s LL hg T₀ T₁ T₂ f g hfg h₀ h₁ h₂ τ a
    obtain ⟨hf, hg', hi, he, hs⟩ := hfg
    have k := h K s LL hg T₀ T₁ T₂ f g
    have k' := k hf hg' hi he hs
    have k'' := k' h₀ h₁ h₂
    have k3 := k'' τ
    have k4 := k3 a
    obtain ⟨k₁, k₂, k₃⟩ := k4
    refine ⟨k₁, fun y => ?_, fun z => ?_⟩
    · have := SetLike.ext_iff.mp k₂ y
      simpa [Submodule.mem_inf, dualExactSequence_mapdR_eq] using this
    · have := SetLike.ext_iff.mp k₃ z
      simpa [dualExactSequence_mapdR_eq] using this

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
theorem _root_.GlobalTheory.DeRhamCompare.strict_iff :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  ⟨strictness_of_dualExactSequence_strict P,
    dualExactSequence_strict_of_strictness P⟩

end GlobalTheory.DeRhamCompare
