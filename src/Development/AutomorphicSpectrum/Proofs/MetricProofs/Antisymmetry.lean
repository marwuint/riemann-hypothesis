import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelation
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyAnalyticSystemExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinear
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNext
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem antisymmetry : Antisymmetry := by
  intro hIn II hII Ψ _ _ _ N j d hN S K _ ι _ P Re hF
  obtain ⟨d₀, S₀, Re₀, hd₀, hdeg₀, href₀, hline₀, ⟨hF₀⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.flagVarieties_flagSys hIn Ψ N hN
  have hdim : d + 1 = antisymDegree Ψ N := hF.dim
  obtain rfl : d = d₀ := by omega
  have hS := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.proportional hIn Ψ N j hN hF.j_le).2 (d + 1) S hdim hF.unif).2
  have hpot := _root_.GlobalTheory.CompanionTheory.Ar.PB.re_pot hIn.2.1.1 (FlBlock Ψ N) (FlIdx Ψ N) (d + 1) (Ψ × Fin N) S₀ (PFl Ψ N) Re₀
  have harith : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]; exact Re₀.arith
  have hfl := flLines_polys hIn II hII Ψ N hN harith

  have hdeg0 : toWt S₀.degPoly = degFlPoly Ψ N := by
    have h2 := hfl.2
    rw [← hdim] at h2
    rw [h2]
    congr 1
    unfold AnSys.degPoly
    congr 1
    funext w
    have h3 := hpot.2.1 w
    simp only [href₀, hdeg₀, Nat.cast_one, one_mul] at h3
    exact h3.symm

  have hPB0 : toWt (Re₀.PB II) = hFlPoly Ψ N II := by
    have h1 := hfl.1
    rw [← hdim] at h1
    rw [h1]
    congr 1
    unfold Realis.PB
    congr 1
    funext w
    unfold Realis.limNum Realis.num
    simp only [hline₀, hdeg₀, Nat.cast_one, div_one]
    exact tendsto_const_nhds.limUnder_eq

  have hdegS : S.degPoly = C (volOf S) * S₀.degPoly := by
    apply (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).2.2 Ψ N
    rw [hS, map_mul, hdeg0]
    congr 1
    simp [toWt, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

  obtain ⟨Cst, hC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound Ψ N (antisymDegree Ψ N + 1)
  have hhomT : (toWt (Re.PB II)).IsHomogeneous (antisymDegree Ψ N + 1) := by
    refine (hC.1 _ 0 ?_).1
    rw [← hdim]
    exact (formPoly_isHomogeneous_and_eval (Ψ × Fin N) (d + 1 + 1) (Re.limNum II)).1
  have hhomH : (hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) :=
    (formPoly_isHomogeneous_and_eval (Ψ × Fin N) _ _).1
  have hhom : (toWt (Re.PB II) - volOf S • hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) := by
    have hm := (homogeneousSubmodule (Ψ × Fin N) ℝ (antisymDegree Ψ N + 1)).sub_mem
      ((mem_homogeneousSubmodule _ _).2 hhomT)
      (Submodule.smul_mem _ (volOf S) ((mem_homogeneousSubmodule _ _).2 hhomH))
    exact (mem_homogeneousSubmodule _ _).1 hm
  refine mem_antisymSpace_of_pointwise Ψ N j _ hhom ?_
  intro τ a b hab hj lam
  have e1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.thmA_swap hIn II hII Ψ N d S K ι P Re τ a b hab (hF.sq τ a b hab hj) lam
  have e0 := _root_.GlobalTheory.CompanionTheory.Ar.PB.thmA_swap hIn II hII Ψ N d S₀ (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) Re₀ τ a b hab
    (hF₀.sq τ a b hab (Or.inl b.isLt)) lam
  rw [hPB0] at e0
  rw [hdegS, (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).2.1, (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).1, Polynomial.eval_mul, Polynomial.eval_C, ← e0] at e1
  simp only [map_sub, smul_eval]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.Top
