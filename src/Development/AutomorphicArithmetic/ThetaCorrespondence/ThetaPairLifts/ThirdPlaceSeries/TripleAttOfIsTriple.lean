import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TripleAttOfIsTripleWith
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
theorem triple_att_n_of_is_triple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀) (hF : FrobDense D)
    (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (s : D.ntw.Sig i) :
    _root_.GlobalTheory.TripleGal.TripleAttN D.naut (bk0 D) i s := by
  obtain ⟨C, art, h⟩ := h
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  exact _root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple_with hF hG h.artin h1 h2 S
end GlobalTheory.TripleLocal
end
end
