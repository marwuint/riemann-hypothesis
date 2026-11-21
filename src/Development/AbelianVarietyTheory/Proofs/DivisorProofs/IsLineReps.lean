import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable (F) in

def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def firstColumn {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => X i 0

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

end GlobalTheory.EisMidHt

end
