import Mathlib

noncomputable section

namespace PI

open Finset

def posAdd {n' : ℕ} (s : Fin n') (e : ℕ) : Fin n' :=
  ⟨(s.val + e) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

end PI

end
