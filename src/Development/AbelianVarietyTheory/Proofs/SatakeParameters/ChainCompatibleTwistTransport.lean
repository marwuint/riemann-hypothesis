import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⟨⟨⟨fun x => ∀ t : Set (Chr F E L), (∃ K : Subgroup (Chr F E L), (fun y => ∀ t' : Set (Chr F E L),
      (∃ _ : (∃ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v) = K), (K : Set (Chr F E L)) = t') → t' y) = t) → t x,
    (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).mul_mem'⟩, (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).one_mem'⟩,
    (⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)).inv_mem'⟩

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    ∀ t : Set (Chr F E L), (∃ K : Subgroup (Chr F E L), (fun y => ∀ t' : Set (Chr F E L),
      (∃ _ : (∃ v, unramOff F E L S v = K), (K : Set (Chr F E L)) = t') → t' y) = t) → t x

end Mem

end GlobalTheory.ColPeriodCompare
