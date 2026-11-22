import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibres
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticeOrbitCountEqSumOrbits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerRelIndexIntUnitsNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitOrbitsStableLatticesSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticePairRelIndexIntegralUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairOrbitsFiniteAndCardProd

open Polynomial

namespace GlobalTheory.UnitLemma.DescentGL

open GlobalTheory.UnitLemma

theorem stab_smul_comm {G X : Type} [CommGroup G] [MulAction G X] (t : G) (x : X) :
    MulAction.stabilizer G (t • x) = MulAction.stabilizer G x := GlobalTheory.OrbitCounting.stabilizer_smul_eq t x

theorem countGL_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  intro O _ _ _ _ E _ _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hsep
  have hs₁ := hsep.of_mul_left
  have hs₂ := hsep.of_mul_right
  have hres : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 :=
    resultant_ne_zero _ _ hsep.isCoprime
  rw [_root_.GlobalTheory.UnitLemma.countGL_eq_sum_orbits O E (A₁ × A₂) (g₁, g₂), _root_.GlobalTheory.UnitLemma.countGL_eq_sum_orbits O E A₁ g₁, _root_.GlobalTheory.UnitLemma.countGL_eq_sum_orbits O E A₂ g₂]
  haveI hf₁ := _root_.GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable O E A₁ g₁ hs₁
  haveI hf₂ := _root_.GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable O E A₂ g₂ hs₂
  obtain ⟨hfinY, hsum⟩ := _root_.GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum O E A₁ A₂ g₁ g₂ hf₁ hf₂
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hfib := _root_.GlobalTheory.UnitLemma.ncard_fibre_latProj O E A₁ A₂ g₁ g₂ hres
  have hstab : ∀ y : LatPair O E g₁ g₂, MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧
      (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) ≠ 0 := by
    intro y
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex O E A₁ A₂ g₁ g₂ y (_root_.GlobalTheory.UnitLemma.stabilizer_le_intUnits O E A₁ g₁ y.1) (_root_.GlobalTheory.UnitLemma.stabilizer_le_intUnits O E A₂ g₂ y.2)
    exact ⟨h1, by rw [h2]; exact mul_ne_zero (_root_.GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero O E A₁ g₁ hs₁ y.1) (_root_.GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero O E A₂ g₂ hs₂ y.2)⟩
  have hfin : ∀ y, (latProj O E g₁ g₂ ⁻¹' {y}).Finite := by
    intro y
    apply Set.finite_of_ncard_ne_zero
    have h := hfib y
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zpow_ne_zero _ hq h.symm
  have hCP := _root_.GlobalTheory.OrbitCounting.counting_principle (A₁ × A₂)ˣ (stLat O E ((g₁, g₂) : A₁ × A₂)) (LatPair O E g₁ g₂) (intUnits O (A₁ × A₂))
    (latProj O E g₁ g₂) (_root_.GlobalTheory.UnitLemma.latProj_smul O E A₁ A₂ g₁ g₂) hfin hstab hfinY (fun _ => 1) (fun _ _ => rfl)
  simp only [one_mul] at hCP
  rw [hCP]
  have hterm : ∀ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂),
      ((latProj O E g₁ g₂ ⁻¹' {Quotient.out o}).ncard : ℚ) *
        ((MulAction.stabilizer (A₁ × A₂)ˣ (Quotient.out o)).relIndex (intUnits O (A₁ × A₂)) : ℚ) =
      (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) *
        (((MulAction.stabilizer A₁ˣ (Quotient.out o).1).relIndex (intUnits O A₁) : ℚ) *
          ((MulAction.stabilizer A₂ˣ (Quotient.out o).2).relIndex (intUnits O A₂) : ℚ)) := by
    intro o
    rw [hfib, (_root_.GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex O E A₁ A₂ g₁ g₂ _ (_root_.GlobalTheory.UnitLemma.stabilizer_le_intUnits O E A₁ g₁ _) (_root_.GlobalTheory.UnitLemma.stabilizer_le_intUnits O E A₂ g₂ _)).2, Nat.cast_mul]
  have hs := hsum (fun y => ((MulAction.stabilizer A₁ˣ y).relIndex (intUnits O A₁) : ℚ))
    (fun y => ((MulAction.stabilizer A₂ˣ y).relIndex (intUnits O A₂) : ℚ))
    (fun t y => by simp only [stab_smul_comm]) (fun t y => by simp only [stab_smul_comm])
  rw [finsum_congr hterm, ← mul_finsum, hs]

end GlobalTheory.UnitLemma.DescentGL
