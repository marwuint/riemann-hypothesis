import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.BCWords

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a N c : ℕ} {n : Fin c → ℕ}

def tensorSp (V : ∀ i, Submodule ℂ (Sm E (n i))) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, V i, F = fun m => ∏ i, (φ i).1.1 (m i)}

def InInd (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (φ : Sm E N) : Prop :=
  (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, φ.1 (u * g) = φ.1 g) ∧
    φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) ∧ φ ∈ finVec (cptRep E N) ∧
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => φ.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorSp V

theorem inInd_iff (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (φ : Sm E N) :
    InInd h (fun i => (π i).V) φ ↔ φ ∈ indForms h π := Iff.rfl

end Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.BCWords

end
