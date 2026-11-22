import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.IsGalGen

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def PartA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (Ps : ∀ i, CG E (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps

end PositivityTheory.Rg.Tf.ChR
