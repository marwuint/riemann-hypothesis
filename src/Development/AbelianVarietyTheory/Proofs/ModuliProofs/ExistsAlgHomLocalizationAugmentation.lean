import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    _root_.GlobalTheory.TorsionPres.local_presentation O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    _root_.GlobalTheory.exists_integral_of_local_presentation O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := _root_.GlobalTheory.TorsionTheta.exists_theta O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (_root_.GlobalTheory.dvd_trace_of_balanced_tensor O H Θ (ε l) hΘ h)

end GlobalTheory
