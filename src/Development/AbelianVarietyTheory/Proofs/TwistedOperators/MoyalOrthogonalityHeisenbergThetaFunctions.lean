import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessOrthogonalLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffPolynomialDecayRealDirections
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffHeisenbergTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.MoyalTheta

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  intro D ψ hψ S T v f f₀ hf hf₀
  have hv : IsCovolOne (ratL T S) v.μ v.𝓕 := v.covol
  obtain ⟨hμ, h𝓕, h1⟩ := hv
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : IsTopologicalAddGroup (WO S T) := i1
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : DiscreteTopology (ratL T S) := i5
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨-, -, -, -, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hcc := _root_.GlobalTheory.MatCoefCont.continuous_thPair_heisO D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.LatticeTranslateSum.sum_translates_bounded D ψ hψ θ hθ S T _ (_root_.GlobalTheory.MatCoefLevel.matCoef_level D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
    (_root_.GlobalTheory.RealDecay.realDecay D ψ hψ θ hθ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
  have hint : Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ :=
    GlobalTheory.T.integrable_of_tsum_norm_translate_le (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 (by rw [h1]; exact ENNReal.one_lt_top) _ hcc C hC
  refine ⟨hint, fun x => ?_⟩
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hgc : Continuous fun w => heisO ψ S T w f₀ x := by
    unfold heisO
    exact (hψ.1.1.comp (hcont.comp (continuous_const.prodMk continuous_id))).mul
      (hf₀.cont.comp (continuous_const.add continuous_id))
  obtain ⟨-, ⟨B, hB⟩, -⟩ := GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀
  have hgb : ∃ B : ℝ, ∀ w, ‖heisO ψ S T w f₀ x‖ ≤ B :=
    ⟨B, fun w => by rw [GlobalTheory.ThetaSquare.norm_heisO hψ]; exact hB _⟩
  rw [_root_.GlobalTheory.unfold_integral_fundamentalDomain (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 _ _ hint hgc hgb]
  simp_rw [_root_.GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀ _ x (hC _).1]
  have e : ∀ w, f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x = f x * (f₀ (w + x) * star (f₀ (w + x))) := by
    intro w
    have hu : star (ψ (symplOH S T x w)) * ψ (symplOH S T x w) = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    unfold heisO
    rw [star_mul, add_comm x w]
    linear_combination (f x * f₀ (w + x) * star (f₀ (w + x))) * hu
  simp_rw [e]
  rw [integral_const_mul]
  have hper : ∀ γ ∈ ratL T S, ∀ w : WO S T, f₀ (γ + w) * star (f₀ (γ + w)) = f₀ w * star (f₀ w) := by
    rintro _ ⟨γ, rfl⟩ w
    have hq := hf₀.quasi γ w
    have hu : ψ (-(symplOH S T (ratW T S γ) w)) * star (ψ (-(symplOH S T (ratW T S γ) w))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    change f₀ (ratW T S γ + w) * star (f₀ (ratW T S γ + w)) = _
    rw [hq, star_mul]
    linear_combination (f₀ w * star (f₀ w)) * hu
  rw [GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) v.μ v.𝓕 h𝓕 (fun w => f₀ w * star (f₀ w)) hper x]
  unfold thPair
  ring

end GlobalTheory.MoyalTheta

end
