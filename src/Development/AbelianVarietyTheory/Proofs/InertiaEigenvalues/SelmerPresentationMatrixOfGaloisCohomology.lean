import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrixStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

theorem oneMatrix_of_galoisCohomology :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar →
    UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching →
    ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
      (bkP : BKPh X), ThmS bkP := by
  intro _ hPT hCD _ hLF hLT hLE hGF hGE _ hadm D N X bkP
  refine _root_.GlobalTheory.SelAssemble.thmS_of_selmer_functor GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix D N X bkP ?_
  intro i s Λ _ _ _ κ Q hS
  have hN := GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup D N X bkP i s Λ κ Q hS
  have hU := _root_.GlobalTheory.LocalSaturation.main hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  have hC := _root_.GlobalTheory.LocalConditionCount.locCount hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  exact ⟨GlobalTheory.SelFun.selMaps D N X bkP i s Λ κ Q,
    _root_.GlobalTheory.SelLeftExact.selmer_left_exact D N X bkP i s Λ κ Q hS hN hU,
    GlobalTheory.SelFun.Colim.selColim D N X bkP i s Λ κ Q hS hN hU,
    _root_.GlobalTheory.SelObstruction.selObs hPT hCD hLF hLT hLE hGF hGE D N X bkP i s Λ κ Q hS hN hU hC⟩

end GlobalTheory.SelFun
