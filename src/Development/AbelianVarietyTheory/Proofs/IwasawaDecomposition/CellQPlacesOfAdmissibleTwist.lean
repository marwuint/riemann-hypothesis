import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TameUnitOne

open Formalism.L2.NX

theorem tameVal_eq_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ)
    (hopen : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal)
    (hI : ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A P → ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1)
    (u : 𝓞 E) (hu1 : u - 1 ∈ P.asIdeal) : NX.tameVal φ P e u = 1 := by
  have hu : u ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := P.asIdeal.sub_mem h hu1
    simpa using this))
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨hq2, -⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖne : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) (show 0 < Formalism.ConjugateSelfDual.normV P - 1 by omega)
  have hπne : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖne hπ.symm
  have hv : A.valuation ((1 : Formalism.ConjugateSelfDual.G E Ω) π / π - algebraMap E Ω (u : E)) < 1 := by
    rw [AlgEquiv.one_apply, div_self hπne]
    have h1 := (hA (u - 1)).2 hu1
    have e1 : (1 : Ω) - algebraMap E Ω (u : E) = -(algebraMap E Ω (((u - 1 : 𝓞 E)) : E)) := by
      push_cast
      ring
    rw [e1, Valuation.map_neg]
    exact h1
  have hT := GlobalTheory.TameResRead.tameRep_zpow hA (one_mem _) hϖ1 hϖ2 hπ hu hv e
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep φ P e m hopen hm hI _ u hu hT, one_zpow, map_one]

end GlobalTheory.TameUnitOne

namespace GlobalTheory.LevCmp

end GlobalTheory.LevCmp
