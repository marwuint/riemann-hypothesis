import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExCol
import Formalism.PeriodIntegrals.EtaHostFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.UnitaryNorms.RealPl

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Col

namespace HeckeEx

open Formalism.L2.Host Formalism.L2.Host.CharEx

section Gen

variable {L : Type} [Field L] [NumberField L]

def resU (w : HeightOneSpectrum (𝓞 L)) (y : 𝓞 L) (hy : y ∉ w.asIdeal) : (𝓞 L ⧸ w.asIdeal)ˣ :=
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  Units.mk0 (Ideal.Quotient.mk w.asIdeal y) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])

def TameSpec (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L) (c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ) (lam : (w.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  (∀ x : Lˣ, (x : L) = (ϖ : L) → lam (atFin w x) = 1) ∧
  (∀ x, IsUnitAt w x → ‖((lam x : ℂˣ) : ℂ)‖ = 1) ∧
  (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) → lam x = 1) ∧
  (∀ (x : Lˣ) (y : 𝓞 L) (cl : (𝓞 L ⧸ w.asIdeal)ˣ), (x : L) = (y : L) →
    (cl : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → lam (atFin w x) = c cl)

def TameLocEx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 →
    ∀ c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, ∃ lam : (w.adicCompletion L)ˣ →* ℂˣ, TameSpec w ϖ c lam

end Gen

section Col

variable {X : Fields}

theorem hxConjO_invol (X : Fields) (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show star (star (x : X.E)) = x
  exact star_star _

def cP (X : Fields) (w : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have h1 : X.conjO p ∈ w.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, hxConjO_invol X]; exact hp
    rw [h, Ideal.mem_bot] at h1
    apply hp0
    rw [← hxConjO_invol X p, h1, map_zero]

theorem mem_cP (w : HeightOneSpectrum (𝓞 X.E)) (r : 𝓞 X.E) : r ∈ (cP X w).asIdeal ↔ X.conjO r ∈ w.asIdeal := Iff.rfl

variable {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (j : Fin m)

variable (hT : TameLocEx)

variable {Ch σ₀ j hT}

variable (Ch σ₀ j hT)

end Col

end HeckeEx

end Formalism.L2.Col
