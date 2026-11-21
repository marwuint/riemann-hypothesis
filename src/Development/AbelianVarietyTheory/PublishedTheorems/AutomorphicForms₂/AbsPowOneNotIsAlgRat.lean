import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal.Model

variable (E : Type) [Field E] [NumberField E]

def absPow (s : ℝ) : HChar E :=
  ⟨GlobalTheory.Mem.Chr.CharModel.absHom E s, (GlobalTheory.Mem.Chr.CharModel.absChar E s).2⟩

theorem absPow_isAbsPow (s : ℝ) : (absPow E s).IsAbsPow s :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) s

theorem frob_abs {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {m : ℕ} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι (absPow E m) n r) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) ^ m := by
  rw [h.frob_unr ha (Or.inl hv) ((absPow_isAbsPow E m).1 v) hA hσ, (absPow_isAbsPow E m).2.1 v,
    Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀, inv_inv, map_pow, map_natCast]
  rfl

end GlobalTheory.HeckeGal.Model

end
