import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace GlobalTheory.Mem.Cert

noncomputable def powMod (a m k : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 1) (fun _ ih e => (ih (e / 2) ^ 2 * a ^ (e % 2)) % m) k

theorem powMod_succ (a m k e : ℕ) : powMod a m (k + 1) e = (powMod a m k (e / 2) ^ 2 * a ^ (e % 2)) % m := rfl

end GlobalTheory.Mem.Cert

namespace GlobalTheory.Mem.Explicit

end GlobalTheory.Mem.Explicit

end
