import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Triv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem det_eq_one_fin_one (g : Matrix (Fin 1) (Fin 1) ℂ) (h : g.det = 1) : g = 1 := by
  ext i j
  fin_cases i; fin_cases j
  rw [Matrix.det_unique] at h
  simpa using h

instance subsingleton_SUJ (ε : Fin 1 → Bool) : Subsingleton (SUJ ε) :=
  ⟨fun a b => Subtype.ext (Subtype.ext (Units.ext
    ((det_eq_one_fin_one _ a.2).trans (det_eq_one_fin_one _ b.2).symm)))⟩

end GlobalTheory.DSSU.Triv
