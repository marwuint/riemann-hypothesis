import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace DivCycleGeneric

open MvPolynomial

section Generic

variable {n : ℕ}

def blkEquiv (n : ℕ) : (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ≃ Fin n where
  toFun p := p.2
  invFun := blk n
  left_inv _ := rfl
  right_inv _ := rfl

def toGeneric (n : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n) →+* MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename (R := ℤ) (blkEquiv n)).toRingHom

abbrev genericAlgebra (n : ℕ) :
    Algebra (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) :=
  (toGeneric n).toAlgebra

attribute [local instance] genericAlgebra

abbrev intUnits (n : ℕ) : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))

instance isLocalization_generic (n : ℕ) : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) (R := ℤ) (S := ℚ)
  have : IsLocalization (intUnits n) (MvPolynomial (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ℚ) :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  refine IsLocalization.isLocalization_of_algEquiv (intUnits n)
    (AlgEquiv.ofRingEquiv (f := (renameEquiv ℚ (blkEquiv n)).toRingEquiv) fun x => ?_)
  show (renameEquiv ℚ (blkEquiv n)) (MvPolynomial.map (algebraMap ℤ ℚ) x) =
    MvPolynomial.map (Int.castRingHom ℚ) (rename (blkEquiv n) x)
  rw [renameEquiv_apply, map_rename, algebraMap_int_eq]

end Generic

end DivCycleGeneric

end ObjectsChow

end GroundTheory.Heights₂.Heights
