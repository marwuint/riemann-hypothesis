import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingCoeffFieldAndNumbeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterValuesIntegralUnitsAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsOverRealPlacesAndConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimePlacesIsSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorIntegralOnLatticeAtTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorsOnLocalisationSpaceSemisimple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsFaithfullyOnLocalisedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsOnLatticeAsOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveLStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

def feSup {l : ℕ} [Fact l.Prime] (K L : Loc.FinExt l) : Loc.FinExt l :=
  ⟨K.1 ⊔ L.1, haveI := K.2; haveI := L.2; IntermediateField.finiteDimensional_sup _ _⟩

theorem osInt (D : D7) (B : LocBase0 D.host D.what₂) : OsInt B := fun j w y =>
  IsIntegrallyClosed.isIntegral_iff.1 <| by
    obtain ⟨p, hp, h0⟩ := D.O_int y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim (RingHom.comp _ _) ((B.ec j w).comp (algebraMap ℤ D.what₂.LL)), ← hom_eval₂, h0, map_zero]

theorem plGwDisj (D : D7) : PlGwDisj D := by
  have key : ∀ v v', D.naut.plGw 0 v ≠ D.naut.plGw 1 v' := fun v v' e => by
    have h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 0 v).asIdeal := D.naut.plGw_over 0 v
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 1 v').asIdeal := D.naut.plGw_over 1 v'
    rw [← e] at h1
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne).cast
    exact (D.naut.plGw 0 v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  intro k k' v v' e
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd e (key v v')
  · exact absurd e.symm (key v' v)
  · rfl

section Psi

variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)

theorem psN_spec (g : G D.host.E D.nd.Om) : algebraMap (OcC X j w) (FractionRing (OcC X j w)) (psN X ψ0 hP j w g : OcC X j w) =
    ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
  unitsLift_spec ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w) g

include hψ0 in

theorem psN_eq_one (g : G D.host.E D.nd.Om) : psN X ψ0 hP j w g = 1 ↔ ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) g = 1 := by
  rw [← Units.val_eq_one, ← map_eq_one_iff _ (IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))), psN_spec,
    map_eq_one_iff _ (ecC X j w).injective, ← map_eq_one_iff _ (C.embW w).injective, hψ0,
    map_eq_one_iff _ (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))), map_eq_one_iff _ (C.Oe_inj w),
    Units.val_eq_one]
  rfl

include hψ0 in
theorem psN_of_art {g : G D.host.E D.nd.Om} (h : D.ntw.art (C.twI w) (C.Q w) g = 1) : psN X ψ0 hP j w g = 1 := by
  rw [psN_eq_one hψ0, MonoidHom.comp_apply, h, map_one]

include hψ0 in
theorem psN_ord (g : G D.host.E D.nd.Om) : ∃ n : ℕ, psN X ψ0 hP j w g ^ (D.what₂.places.resChar w ^ n) = 1 := by
  obtain ⟨n, hn⟩ := D.ntw.RCG_l _ _ (D.ntw.art (C.twI w) (C.Q w) g)
  rw [C.twI_l, ← map_pow] at hn
  exact ⟨n, by rw [← map_pow]; exact psN_of_art hψ0 hP j w hn⟩

include hψ0 in
theorem psN_open : IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om)) :=
  Subgroup.isOpen_mono (H₁ := (D.ntw.art (C.twI w) (C.Q w)).ker) (fun _ hg => psN_of_art hψ0 hP j w hg) (D.ntw.art_cont _ _)

include hψ0 in
theorem psN_anti : AntiHom D.ntw.cc (psN X ψ0 hP j w) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact psN_of_art hψ0 hP j w (by rw [map_mul, D.ntw.art_anti _ _ g g' h, inv_mul_cancel])

include hψ0 in
theorem psN_ram (h : ∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) :
    RamExactly (psN X ψ0 hP j w) (↑(C.Q w) : Set (HeightOneSpectrum (𝓞 D.host.E))) := fun v A hA => by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    by_contra hv
    exact hne (psN_of_art hψ0 hP j w (D.ntw.art_unr _ _ v hv A hA σ hσ))
  · intro hv
    obtain ⟨σ, hσ, hne⟩ := h v hv A hA
    exact ⟨σ, hσ, fun e => hne ((psN_eq_one hψ0 hP j w σ).1 e)⟩

end Psi

end GlobalTheory.HeckeLocN
