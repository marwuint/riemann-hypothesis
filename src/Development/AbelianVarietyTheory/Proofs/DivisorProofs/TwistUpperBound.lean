import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TupLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem baseOf_of_pin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.BigOn.Exp.TupLe

end
