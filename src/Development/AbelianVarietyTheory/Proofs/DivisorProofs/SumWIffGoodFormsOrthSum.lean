import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.SumWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := RingOfIntegers.ext (star_star (x : E))

theorem cj_algMap (hc : CMData F E) (x : 𝓞 F) : cj E (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
  RingOfIntegers.ext ((hc.fixed _).2 ⟨x, rfl⟩)

theorem exists_norm (hc : CMData F E) (y : 𝓞 E) : ∃ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) x = y * cj E y := by
  obtain ⟨a, ha⟩ := (hc.fixed ((y * cj E y : 𝓞 E) : E)).1 (by
    rw [← cj_coe, map_mul, cj_cj, mul_comm])
  have hi : IsIntegral ℤ a := by
    have h1 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact (y * cj E y).isIntegral_coe
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨a, hi⟩, RingOfIntegers.ext ha⟩

end Places

variable {D : D7}

theorem goodAt_comp {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ} {ι κ J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ))
    (e : ι → κ) (he : Function.Surjective e) (s : κ → LevelCuspCharacters.SSParam p K r) :
    LevelCuspCharacters.GoodAt χ (fun v => s (e v)) ↔ LevelCuspCharacters.GoodAt χ s := by
  simp only [LevelCuspCharacters.GoodAt, he.forall, he.exists]

theorem coeff_centralIdem {G : Type} [Group G] [Finite G] (τ : G → ℂ) (x : G) :
    (LevelCuspCharacters.centralIdem τ).coeff x = τ 1 / (Nat.card G : ℂ) * τ x⁻¹ := by
  classical
  unfold LevelCuspCharacters.centralIdem
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

end GlobalTheory.SumWCompare
