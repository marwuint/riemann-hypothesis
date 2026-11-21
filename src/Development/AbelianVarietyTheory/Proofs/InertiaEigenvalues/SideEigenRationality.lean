import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LargeO

def sysPol (n : ℕ) {E : Type} [Field E] [NumberField E] (c : HeightOneSpectrum (𝓞 E) → ℕ → ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((normV v : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c v k) * X ^ (n - k)

def BigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (Sf : Finset ℂ) : Prop :=
  ∀ c ∈ Es, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ Sf, ι.symm z ∈ K) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar l),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l))) → IsSSRep ρ →
      (∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
          IsFrob (F := D.host.E) B (normV v) σ →
          ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)).charpoly.map ι.toRingHom = sysPol D.R.nV c v) →
      ∃ Pm : GL (Fin D.R.nV) (Qbar l), ∀ g s t,
        ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)) s t ∈ K

theorem bigOk_mono {D : D7} {l : ℕ} [Fact l.Prime] {Q : Finset (PlE D.host)} {Es : Set (PlE D.host → ℕ → ℂ)}
    {ι : Qbar l ≃+* ℂ} {Sf Sf' : Finset ℂ} (h : BigOk D l Q Es ι Sf) (hs : Sf ⊆ Sf') : BigOk D l Q Es ι Sf' :=
  fun c hc K hK => h c hc K fun z hz => hK z (hs hz)

theorem bigOk_cast {D : D7} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (e : p = q) {Q : Finset (PlE D.host)}
    {Es : Set (PlE D.host → ℕ → ℂ)} {ι : Qbar p ≃+* ℂ} {Sf : Finset ℂ} (h : BigOk D p Q Es ι Sf) :
    BigOk D q Q Es (qCast e ι) Sf := by
  subst e; exact h

theorem exists_bigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (hE : Es.Finite) (hch : GlobalTheory.RowTie.ChebSplit D.nd) : ∃ Sf, BigOk D l Q Es ι Sf := by
  classical
  let Good : PlE D.host → Prop := fun v =>
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q
  let U : Set (G D.host.E D.nd.Om) := {σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}
  have hU : Dense U := GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch
  let p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun c σ =>
    if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0
  have hS := fun c => _root_.GlobalTheory.FrobSysCoef.main l ι D.host.E D.nd.Om D.R.nV U (p c) hU
  choose Sc hSc using hS
  refine ⟨hE.toFinset.biUnion Sc, ?_⟩
  intro c hc K hK ρ hcont hss hchar
  refine hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_
  intro σ hσ
  simp only [p, dif_pos hσ]
  obtain ⟨hg, B, hB, hF⟩ := Classical.choose_spec hσ
  exact hchar _ hg B σ hB hF

theorem charpoly_pt : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.nd.l i) ∧
      v ∉ placesS D (D.nd.l i) ∧ v ∉ D.nd.Q i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
        sysPol D.R.nV (ptSys D i x) v := by
  intro D i x ρ hρ v hv B σ hB hF
  have hso : SplitOut D.nd i v := ⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩
  rw [hρ.2.2 v hso B σ hB hF, Polynomial.map_map]
  have hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i := rfl
  rw [hcomp]
  unfold heckePol sysPol
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hg : GenAt D (D.nd.l i) (D.nd.Q i) v k := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩
  simp only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul,
    map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

theorem model_of_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (P : GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ →
    (∀ g s t, ∃ x, A.iotaQ i x = ((P⁻¹ * ρ g * P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) →
    ∃ (r : G H.E N.Om →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ P hc hP
  let ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)) := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P := fun g => by
    simp [ρ', MulAut.conj_apply]
  have hc' : SumRepresentations.At.ContQ N i ρ' := by
    unfold SumRepresentations.At.ContQ at hc ⊢
    have e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) =
        fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) := by
      funext g; rw [hρ']; rfl
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, Pm, hr⟩ := _root_.GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)
  refine ⟨r, P * Pm, fun g => ?_⟩
  rw [hr g, hρ', mul_inv_rev]
  group

end GlobalTheory.LargeO
