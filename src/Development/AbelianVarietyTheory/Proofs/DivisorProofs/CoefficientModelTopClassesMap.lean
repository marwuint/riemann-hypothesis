import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorCharacterScaledTable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeries

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerConjTransport

theorem kkMap_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    {N : Std G U} (Z : Normal W N) (t : T) (j : ℕ) (d : FinDatum G t (.top t j)) (x : FinPt G (Pair.top t j).small)
    (y : FinPt G (Pair.top t j).big) (Hf : VC D (G.pS (Pair.top t j)).rank (G.pT (Pair.top t j)).rank → ℂ)
    (hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (Pair.top t j).small) (wt G (Pair.top t j).big) (nuEnd G (.top t j)))
    (hper : ∀ τ : D.what₂.Tau, period Z.δ τ ≠ 0)
    (hjet : ∀ mon, jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) mon = Z.c0 (.top t j) * opp (.top t j : Pair T)
       (((mon.mapDomain (fvar G (.top t j))).prod fun v e => period Z.δ v.1 ^ e) *
         GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G (.top t j))) 1) Hf)) :
    Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G (Pair.top t j).small) (wt G (Pair.top t j).big)
      (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) Hf) (nuEnd G (.top t j)) := by
  have e1 : jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) = fun mon => (Z.c0 (.top t j) : ℂ) *
      ((mon.prod fun v e => period Z.δ v.1 ^ e) * GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) Hf) := by
    funext mon
    rw [hjet mon, show fvar G (Pair.top t j) = id from rfl, Finsupp.mapDomain_id]
    rfl
  unfold Normal.kkMap fockComp
  rw [e1, _root_.GlobalTheory.JetCharScale.jetOp_scale _ _ _ _ _ _ hJ, smul_smul]
  have hs : Z.scal 1 (Pair.top t j) * ((Z.c0 (Pair.top t j) : ℂ) *
      ∏ τ, period Z.δ τ ^ ∑ i, (wt G (Pair.top t j).big τ).natW i) = 1 := by
    unfold Normal.scal GlobalTheory.FunObj.fockDeg
    simp only [opp, RingHom.id_apply, Pi.one_apply, one_div]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    simp only [← mul_pow, inv_mul_cancel₀ (hper _), one_pow, Finset.prod_const_one, mul_one]
    simp
  rw [hs, one_smul]

end GlobalTheory.KerConjTransport

end
