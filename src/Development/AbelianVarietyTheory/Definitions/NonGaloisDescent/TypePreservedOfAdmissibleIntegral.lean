import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ReadingAllLemmas

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll.Model

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X}

theorem zpow_apply' (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : X.RCG i Q →* (X.Ok i k)ˣ) (a : ℤ)
    (g : X.RCG i Q) : (ψ ^ a) g = (ψ g) ^ a := rfl

theorem provedGaloisAll_iff {E : ExpDat Y} {N0 : X.Tw → ℕ} {i : X.Tw} :
    goodTwistExistsAllCoprimePowers Y bkP E N0 i ↔ GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces.LemmaAllAt Y bkP E N0 i := Iff.rfl

variable (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

end GlobalTheory.TwAll.Model

end
