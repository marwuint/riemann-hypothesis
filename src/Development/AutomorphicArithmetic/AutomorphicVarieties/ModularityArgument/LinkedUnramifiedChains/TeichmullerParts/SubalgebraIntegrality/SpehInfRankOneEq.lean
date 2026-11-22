import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumHodgeTate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumTwoOfHodgeTate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumFamilyOfReductions
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EtaCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompatiblePolarizationOfLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Mathlib

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af.Gu UpperTheory.V.Z.J.D GlobalTheory.DefiniteBC GlobalTheory.SmGL
open UpperTheory.V.Z.Mult (Cp At)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (e : RepIso r r') (h : IsIrr r) :
    IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let T : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : Formalism.MainNotions.N.IsInv r (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have h1 := hM g _ hv
    have h2 : T ((r g : Matrix (Fin n) (Fin n) k).mulVec v) = (r' g : Matrix (Fin n) (Fin n) k).mulVec (T v) := by
      rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
      simp [Matrix.mul_assoc]
    show T _ ∈ M
    rw [h2]
    exact h1
  rcases h.2.2 _ le_top hi with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by simpa using hv
    rw [h0] at h1
    simpa using (Submodule.mem_bot k).1 h1
  · right
    refine (Submodule.eq_top_iff').2 fun v => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by rw [h0]; trivial
    simpa using h1

private theorem iso_split {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (r r' : G E Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hr' : Continuous r')
    (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hc : ∀ g : G E Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G E Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (Filter.eventually_cofinite.1 hw) h1 h2 ?_) g
    intro v hv hd A hA σ hσ
    obtain ⟨B, hB, hB'⟩ := (not_not.1 hv) (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v (hE v) hd)
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem ev_away {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

