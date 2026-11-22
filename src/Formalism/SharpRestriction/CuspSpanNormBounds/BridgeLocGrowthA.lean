import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors

noncomputable section

open MeasureTheory Matrix Finset
open Formalism.REAL Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped ENNReal

namespace Formalism.MainNotions.BridgeLocGrowth

variable {n : ℕ}

def SUJ (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | (toM g).det = 1}
  mul_mem' := by
    intro a b ha hb
    change (toM a * toM b).det = 1
    rw [Matrix.det_mul, show (toM a).det = 1 from ha, show (toM b).det = 1 from hb, one_mul]
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ).det = 1
    exact Matrix.det_one
  inv_mem' := by
    intro a ha
    have ha' : (toM a).det = 1 := ha
    have hm : toM a⁻¹ * toM a = 1 := Units.inv_mul (a : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    change (toM a⁻¹).det = 1
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul, ha', mul_one, Matrix.det_one] at h
    exact h

theorem continuous_toM (ε : Fin n → Bool) : Continuous (fun g : UJ ε => toM g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isClosed_SUJ (ε : Fin n → Bool) : IsClosed (SUJ ε : Set (UJ ε)) :=
  isClosed_eq (continuous_toM ε).matrix_det continuous_const

instance instMeasurableSpaceSUJ (ε : Fin n → Bool) : MeasurableSpace (SUJ ε) := borel _

instance instBorelSpaceSUJ (ε : Fin n → Bool) : BorelSpace (SUJ ε) := ⟨rfl⟩

instance instLocallyCompactSUJ (ε : Fin n → Bool) : LocallyCompactSpace (SUJ ε) :=
  (isClosed_SUJ ε).isClosedEmbedding_subtypeVal.locallyCompactSpace

def KSU (ε : Fin n → Bool) : Subgroup (SUJ ε) := (KG ε).comap (SUJ ε).subtype

instance instCompactKSU (ε : Fin n → Bool) : CompactSpace (KSU ε) := by
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    have h := isCompact_range (continuous_subtype_val : Continuous (Subtype.val : KG ε → UJ ε))
    rwa [Subtype.range_coe] at h
  have h1 : IsCompact ((KG ε : Set (UJ ε)) ∩ SUJ ε) := hK.inter_right (isClosed_SUJ ε)
  have he : Topology.IsEmbedding (fun k : KSU ε => ((k : SUJ ε) : UJ ε)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have himg : (fun k : KSU ε => ((k : SUJ ε) : UJ ε)) '' Set.univ = (KG ε : Set (UJ ε)) ∩ SUJ ε := by
    ext g
    constructor
    · rintro ⟨k, -, rfl⟩
      exact ⟨k.2, (k : SUJ ε).2⟩
    · rintro ⟨hk, hs⟩
      exact ⟨⟨⟨g, hs⟩, hk⟩, trivial, rfl⟩
  rw [← himg] at h1
  exact isCompact_univ_iff.mp (he.isInducing.isCompact_iff.mpr h1)

instance instMeasurableSpaceKSU (ε : Fin n → Bool) : MeasurableSpace (KSU ε) := borel _

instance instBorelSpaceKSU (ε : Fin n → Bool) : BorelSpace (KSU ε) := ⟨rfl⟩

end Formalism.MainNotions.BridgeLocGrowth
