import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

open NumberField

noncomputable section

namespace UpperTheory.HF.Formalism.HC.HostRaw

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

instance muW_neZero : NeZero H.w := ⟨H.w_pos.ne'⟩

end UpperTheory.HF.Formalism.HC.HostRaw

end
