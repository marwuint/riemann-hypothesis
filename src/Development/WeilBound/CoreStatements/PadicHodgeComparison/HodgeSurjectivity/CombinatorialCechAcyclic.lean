import Mathlib

set_option autoImplicit false

noncomputable section

namespace CechCochains.H4

variable {d : ℕ} (M : Type) [AddCommGroup M]

def Coch (T : Finset (Fin d)) (p : ℕ) : Type := {I : Finset (Fin d) // T ⊆ I ∧ I.card = p + 1} → M

instance (T : Finset (Fin d)) (p : ℕ) : AddCommGroup (Coch M T p) := inferInstanceAs (AddCommGroup (_ → M))

end CechCochains.H4
