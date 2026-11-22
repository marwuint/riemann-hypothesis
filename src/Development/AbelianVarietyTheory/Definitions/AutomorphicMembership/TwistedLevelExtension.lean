import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Formalism.LocalToGlobal.Columns.ChainLawXiQF
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.TwModel
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

def trv {n : ℕ} {a b : Fin n} (h : a ≠ b) : Sp E n ≃ₗ[E] Sp E n where
  toFun x := x + Pi.single a (x b)
  invFun x := x - Pi.single a (x b)
  map_add' x y := by simp only [Pi.add_apply, Pi.single_add]; abel
  map_smul' c x := by
    funext l
    by_cases hl : l = a
    · subst hl; simp [mul_add]
    · simp [Pi.single_eq_of_ne hl]
  left_inv x := by simp [Pi.single_eq_of_ne h.symm]
  right_inv x := by simp [Pi.single_eq_of_ne h.symm]

end

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m) (m2 : ℕ)

end GlobalTheory.Mem.Col2.TC.TwModel

namespace GlobalTheory.Mem.Col2.TC.TwModel

end GlobalTheory.Mem.Col2.TC.TwModel

end
