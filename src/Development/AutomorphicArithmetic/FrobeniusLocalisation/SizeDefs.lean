import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace UpperTheory.HF.Formalism.HC

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC

namespace Frame

end Frame

namespace HostRaw

open _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def frobG (p : ℕ) : φ.GG :=
  if h : Nat.Coprime p H.condN then H.art (ZMod.unitOfCoprime p h) else 1

def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (-(H.d : ℤ)) p = -1

theorem frobG_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : H.frobG p = H.art (ZMod.unitOfCoprime p h) := dif_pos h

end HostRaw

end UpperTheory.HF.Formalism.HC

end
