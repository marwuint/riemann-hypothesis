import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.DetFibre

section Marks

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem det_cong_of_finCong (V : HSp D) (N : ℕ) (hN : N ≠ 0) (u : GA D V) (hu : FinCong V N u) :
    ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (N : ℕ) • w := by
  obtain ⟨k1, -, k3, k4, -⟩ := _root_.GlobalTheory.Member.latHat_eq_hat_and_gram D V
  exact det_cong_one D.host.F (latC V) k3 k4 N hN (finHom V u).1 (by rw [← k1]; exact hu)

end Marks

end GlobalTheory.DetFibre
