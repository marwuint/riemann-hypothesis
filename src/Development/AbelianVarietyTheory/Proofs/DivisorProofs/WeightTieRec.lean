import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

end GlobalTheory.ColumnNormCompare
