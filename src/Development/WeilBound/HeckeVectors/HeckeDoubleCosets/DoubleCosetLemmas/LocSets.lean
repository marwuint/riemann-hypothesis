import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocMeas
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocCount
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.ExtendedCharacterUnit

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def UnM {n : ℕ} (x : Matrix (Fin n) (Fin n) (Cv v)) : Prop := IntM x ∧ Valued.v x.det = 1

theorem SmM.int {a b : Type} {x : Matrix a b (Cv v)} (h : SmM x) : IntM x := fun i j => (h i j).le

variable [MeasurableSpace (Cv v)] [BorelSpace (Cv v)] {μ : Measure (Cv v)}

end CompanionTheory.D.Upq.DoubleCosetLemmas
