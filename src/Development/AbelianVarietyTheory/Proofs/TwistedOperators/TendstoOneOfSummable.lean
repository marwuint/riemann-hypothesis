import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitarySphericalReps
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadraticStatement

noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

end Analysis

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}

theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)

end Global

end GlobalTheory.LPositivity

end
