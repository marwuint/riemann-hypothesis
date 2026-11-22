import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

namespace GlobalTheory.Mem.Cert

noncomputable def powMod (a m k : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 1) (fun _ ih e => (ih (e / 2) ^ 2 * a ^ (e % 2)) % m) k

end GlobalTheory.Mem.Cert

namespace GlobalTheory.Mem.Explicit

end GlobalTheory.Mem.Explicit

end
