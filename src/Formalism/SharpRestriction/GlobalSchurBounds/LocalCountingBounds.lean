import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace Formalism.MainNotions.UnusedSlot34

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))

def SWa1 : Prop :=
  AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 => μ 𝓕 < ⊤

end Ext

def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J

section Data

open Formalism.BasicNotions

theorem isCMExt_D (D : D7) :
    letI := D.host.cmStar; IsCMExt D.host.F D.host.E D.sp.cm.sig := by
  let _ := D.host.cmStar
  exact ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

end Data

end Formalism.MainNotions.UnusedSlot34
