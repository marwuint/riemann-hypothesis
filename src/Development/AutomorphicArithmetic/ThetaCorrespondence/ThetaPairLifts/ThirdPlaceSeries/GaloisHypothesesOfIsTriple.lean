import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfAttached
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TripleAttOfIsTriple
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

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
theorem adm1_adm8_selfDual_noJump_of_isTriple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀)
    (hF : FrobDense D) (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h2 : BlochKatoReduction.adm2 D) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    BlochKatoReduction.adm1 (bk0 D) ∧ BlochKatoReduction.adm8 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump (bk0 D) i s :=
  _root_.GlobalTheory.TripleGal.adm1_adm8_selfDual_noJump_of_tripleAttN D (bk0 D) hF (fun _ _ => ⟨_, ⟨D.locT _⟩⟩) h2 (_root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple S hF hG h)
end GlobalTheory.TripleLocal
end
end
