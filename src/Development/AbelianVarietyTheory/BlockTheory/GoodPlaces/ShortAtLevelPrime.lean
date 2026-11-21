import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShortPlaceDegreesAtLevelPrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

def Oriented (T : Full D) (i : Fin 2) (π : 𝓞 D.host.E) : Prop :=
  π * T.Q.H.bar π = (D.host.g i : 𝓞 D.host.E) ∧ T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar π}

theorem Oriented.ne_zero {T : Full D} {i : Fin 2} {π : 𝓞 D.host.E} (h : Oriented T i π) :
    π ≠ 0 ∧ T.Q.H.bar π ≠ 0 := by
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime i).ne_zero
  rw [← h.1] at hg
  exact mul_ne_zero_iff.1 hg

end GlobalTheory.IndefiniteRowSideFullHecke.ShortPlaceDegreesAtLevelPrime
