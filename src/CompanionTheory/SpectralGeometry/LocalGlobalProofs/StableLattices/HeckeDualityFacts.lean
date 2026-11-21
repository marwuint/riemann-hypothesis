import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.Dual

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

def twE {A : Type*} [Ring A] (E : Fin n → Fin n → A) (a b : Fin n) : A := -E b a

theorem glRel_twE {A : Type*} [Ring A] {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (twE E) := by
  intro a b c d
  have := h b a d c
  simp only [twE, neg_mul_neg]
  rw [this]
  clear this
  have k1 : (a = d) ↔ (d = a) := eq_comm
  have k2 : (c = b) ↔ (b = c) := eq_comm
  simp only [k1, k2]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel

def tw (X : GMod n) : GMod n := ⟨X.V, twE X.E, glRel_twE X.gl⟩

end GlobalTheory.CompanionTheory.RgExhHecke.Dual
