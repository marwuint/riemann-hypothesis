import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def ImQ (E : Type) [Field E] (d : ℕ) : Prop :=
  0 < d ∧ ∃ x : E, x ^ 2 = -(d : E)

def SqAt (d q : ℕ) [Fact q.Prime] : Prop :=
  IsSquare (-(d : ℚ_[q]))

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def UsPl (d : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  IsSplitAt w ∧ ∀ (q : ℕ) (hq : q.Prime), ((q : ℕ) : 𝓞 E) ∈ w.asIdeal → @SqAt d q ⟨hq⟩

def ApartAll (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u ∈ S, Apart w u

end GlobalTheory.CongL

end
