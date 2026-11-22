import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine _root_.GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [_root_.GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := GlobalTheory.T.quantum_det_adjoint_form π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (_root_.GlobalTheory.CompanionTheory.Clozel.glRel_EopV E a π _) (_root_.GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add, map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
