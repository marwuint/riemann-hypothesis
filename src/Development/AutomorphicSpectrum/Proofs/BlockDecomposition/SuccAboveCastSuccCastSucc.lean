import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeSM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qminor_restrict {n m t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (a b : Fin t → Fin m) (w : ℂ) :
    qminor (fun a b => E (ι a) (ι b)) a b w = qminor E (ι ∘ a) (ι ∘ b) w := by
  unfold qminor Tm
  simp only [Function.comp, hι.eq_iff]

end GlobalTheory.CompanionTheory.RgHeSM
