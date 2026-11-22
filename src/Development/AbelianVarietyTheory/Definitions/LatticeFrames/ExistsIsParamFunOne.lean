import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

namespace GlobalTheory.Core.Rk.IP.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_cartan {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n ≃ m) {C : Matrix m (Fin n) ℂ}
    {J : Matrix m m ℂ} {G : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J) (hG : IsUnit G.det)
    (h : Cᴴ * J * C = G) : ∃ s, IsCartanInv G s ∧ C * s = J * C := by
  have h1 : G⁻¹ * Cᴴ * J * C = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h, Matrix.nonsing_inv_mul _ hG]
  generalize G⁻¹ * Cᴴ * J = C' at h1
  have h2 : C * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h3 : C * (C' * J * C) = J * C := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : G * (C' * J * C) = Cᴴ * C := by
    rw [← h, Matrix.mul_assoc, h3, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJ, Matrix.one_mul]
  refine ⟨C' * J * C, ⟨?_, ?_, ?_⟩, h3⟩
  · rw [Matrix.mul_assoc (C' * J), h3, Matrix.mul_assoc C', ← Matrix.mul_assoc J, hJ, Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, h4, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_mul, hJ', h]
  · rw [h4]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have := congrArg (C' *ᵥ ·) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this

theorem gramAt_unit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).map _

theorem isSplit_two (v : FinPl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w, hw⟩
  · exact hs
  · exfalso
    unfold Formalism.UG.IsInertAt at hw
    obtain ⟨ω, k, hω, hc⟩ := GlobalTheory.SplitIdem.exists_omega D
    let c : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.sp.cm.sig.toRingHom
    have hst : ∀ x ∈ w.asIdeal, c x ∈ w.asIdeal := by
      have : w.asIdeal ≤ w.asIdeal.comap c := by
        conv_lhs => rw [← hw]
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have e : c (algebraMap _ _ a) = algebraMap _ _ a := Subtype.ext (D.sp.cm.sig.commutes a)
        rw [Ideal.mem_comap, Ideal.mem_comap, e, ← hw]
        exact Ideal.mem_map_of_mem _ ha
      exact this
    have hcω : c ω = 1 - ω := RingOfIntegers.ext (by
      change star (ω : D.host.E) = _
      rw [GlobalTheory.SplitIdem.star_eq_conj, hc]; simp)
    have h2' : (2 : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hw, ← map_ofNat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) 2]
      exact Ideal.mem_map_of_mem _ h2
    have hp : ω * (1 - ω) = 2 * k := RingOfIntegers.ext (by
      push_cast at hω ⊢
      simp only [map_mul, map_sub, map_one, map_ofNat, map_natCast]
      linear_combination -hω)
    have hone : ω ∈ w.asIdeal → False := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by have := add_mem h (hcω ▸ hst ω h); rwa [add_sub_cancel] at this))
    rcases w.isPrime.mem_or_mem (hp ▸ Ideal.mul_mem_right _ _ h2') with h | h
    · exact hone h
    · have := hst _ h
      rw [map_sub, map_one, hcω, sub_sub_cancel] at this
      exact hone this

theorem isSphOff_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T}
    {LS : Lat S} {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) (Sf : Finset (FinPl D)) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT Sf Φ ∧ Φ ≠ 0 := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    AddSubgroup.closure_mono fun _ ⟨α, h1, _, h3⟩ => ⟨α, h1, fun _ h => absurd trivial h, h3⟩
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, ⟨fun u hu => h.2.lat.1 u (hle hu), fun e he u hu => h.2.lat.2 e he u (hle hu)⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    exact h.2.fock p.1 p.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h'⟩ := h.2.norm
    simpa [nrm2] using h' p hp

end GlobalTheory.Core.Rk.IP.Model

end
