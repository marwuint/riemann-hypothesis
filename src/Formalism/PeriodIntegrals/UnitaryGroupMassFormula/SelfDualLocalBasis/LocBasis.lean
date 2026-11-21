import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis
import Lemmata.PaddedFamilies.PadFam

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

noncomputable section

namespace PI.SelfDualLoc.W.LB

open PI.SelfDualLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

abbrev Sv : Submonoid (𝓞 E) := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl

lemma Sv_le : Sv (E := E) v ≤ (𝓞 E)⁰ := by
  intro s hs
  obtain ⟨u, hu, rfl⟩ := hs
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (zero_mem _)
  apply hu0
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h)

abbrev Sp : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E (Sv (E := E) v) (Sv_le v)

lemma coe_algebraMap_OF (u : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl

lemma smul_OE (c : 𝓞 E) (w : Fin n → E) : c • w = (c : E) • w := by
  ext j; simp [Algebra.smul_def]

lemma algF_ne_zero {u : 𝓞 F} (hu : u ∉ v.asIdeal) : algebraMap F E (u : F) ≠ 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using h)
    rw [this]; exact zero_mem _
  exact (map_ne_zero_iff _ (algebraMap F E).injective).2 hu0

lemma mem_Sp' (c : E) : c ∈ Sp (E := E) v ↔
    ∃ (a : 𝓞 E) (s : 𝓞 E) (_ : s ∈ Sv (E := E) v),
      c = algebraMap (𝓞 E) E a * (algebraMap (𝓞 E) E s)⁻¹ := Iff.rfl

end PI.SelfDualLoc.W.LB

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc LB

theorem locBasis : LocBasis := by
  first | exact Bl.PaddedFamilies.goal1 .. | (apply Bl.PaddedFamilies.goal1 <;> assumption) | (intros; apply Bl.PaddedFamilies.goal1 <;> assumption)

end PI.SelfDualLoc.W
