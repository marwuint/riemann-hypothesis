import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfParts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeOfConjDualCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.TripleGal
theorem noInv_all_places_alt (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨_root_.GlobalTheory.InvJump.noInv_of_noJump D bkP i s hJ v hl, _root_.GlobalTheory.TateDualInv.noInv_tateDual D bkP i s hT (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact _root_.GlobalTheory.NoLocalInvariants.noInv_of_adm2At D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact _root_.GlobalTheory.TripleGal.ScalarInvariants.noInv_pD D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := _root_.GlobalTheory.TripleGal.pure_of_tripleAtt_n D bkP i s hA
    exact _root_.GlobalTheory.PurityInvariants.noInv_of_pure_n D i s ι hι v hl hS
theorem adm1_adm8_selfDual_noJump_of_tripleAttN : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact _root_.GlobalTheory.NoJumpMult.noJump_of_jumps D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact _root_.GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts D bkP i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s))
      (_root_.GlobalTheory.TripleGal.noInv_all_places_alt D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (_root_.GlobalTheory.TripleGal.negCount_of_goodJ D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h')
  · exact _root_.GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt_n D bkP i s (hA i hi s))
  · exact _root_.GlobalTheory.LatticeSelfDual.selfDual_of_charDual D i s (h2 i hi s) (_root_.GlobalTheory.CharDualDense.charDual_of_frobDual D hF i s (_root_.GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt_n D bkP i s (hA i hi s)))
end GlobalTheory.TripleGal
end
