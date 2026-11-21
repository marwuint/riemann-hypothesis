import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinfty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : Gl l), ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ ∃ γ : TameGal K l e a, Covers K t ϖ (sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ := _root_.GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf l a e ϖ he (sQ l g)
  let h' : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := _root_.GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf l a e ϖ he k hk
  exact _root_.GlobalTheory.CoverGen.exists_covers_of_sigma_teich l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
