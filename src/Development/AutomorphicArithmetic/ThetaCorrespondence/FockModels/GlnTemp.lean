import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnSuff
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TProdExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCosocleUnit
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTCentred
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTOrderfree
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace UpperTheory.Lit.Cas

theorem temperedProduct (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hC : GlobalTheory.Published.StandardCosocleGL) (hM : GlobalTheory.Published.LanglandsMultisegments)
    (hS : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.TemperedProductOfSquareIntegrable := by
  intro k _ _ _ _ _ N hN V _ _ π hs hi
  constructor
  · intro ht
    have hO : Zc.LOrderFree k := orderfree hC hM k
    have hSo : Zc.LSocleGL k := _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL hA (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) hO
    have hL : Zc.LSegExists k := fun Δ => _root_.GlobalTheory.CompanionTheory.LkSegExists.exists_isLSeg hA Δ
    obtain ⟨𝔪, h𝔪⟩ := hE k (IrrGL.of π hs hi)
    have h𝔪' : IsL 𝔪 π := h𝔪.of_equiv (IrrGL.equivOf π hs hi).symm
    obtain ⟨h, x, hd, hx, hu⟩ := _root_.GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary k hSo (Zl.JC.casselmanNecTemp_holds k) hL 𝔪 N π hN hs hi ht h𝔪'
    obtain ⟨Δ, hΔo, hΔ⟩ := hx
    have hsq : ∀ a, IsSqIntCoeff (x a).rep := fun a => centred hS hA k (Δ a) (x a) (hΔ a) (hu a)
    have e := cosocleUnit hBZ k h N x hd V π (fun a => _root_.GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff k (x a) (hsq a)) (hO 𝔪 h N x hd ⟨Δ, hΔo, hΔ⟩ π h𝔪')
    refine ⟨h, x, hd, fun a => ⟨?_, hsq a⟩, e⟩
    have h1 := (hΔ a).deg_eq
    have h2 := Nat.mul_pos (Δ a).len_pos (Δ a).d_pos
    simp only [Segment.deg] at h1
    omega
  · rintro ⟨h, δ, hd, hδ, e⟩
    obtain ⟨hu, hw⟩ := prodExp hG hBZ hA k (Zl.JC.casselmanNecSq_holds k) h N δ hd hδ V π hi e
    have H := casselmanSuffTemp hA hF k N π hN hs hi hu hw
    intro ε hε
    exact H ε hε

end UpperTheory.Lit.Cas

end
