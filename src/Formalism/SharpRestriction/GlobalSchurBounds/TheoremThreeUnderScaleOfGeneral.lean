import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

def DiscreteSeriesDegreeBoundsOfScaleAgreement (D : D7) : Prop := cdScaleTie D → StandardLattice.DiscreteSeriesDegreeBoundsOfGap D

def cdScaleTieR (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((s n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ cdScaleTieR D.cd D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAtScale (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * StandardLattice.lamAbs lam) ^ (p * q)

theorem theorem_three_explicit_iff_scale (D : D7) : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D ↔ DiscreteSeriesDegreeBoundsAtScale D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAllScales : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s → DiscreteSeriesDegreeBoundsAtScale s

theorem theorem_three_under_scale_of_general (h : DiscreteSeriesDegreeBoundsAllScales) (D : D7) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))

variable {eps : ℝ}

end Formalism.MainNotions.RT

end
