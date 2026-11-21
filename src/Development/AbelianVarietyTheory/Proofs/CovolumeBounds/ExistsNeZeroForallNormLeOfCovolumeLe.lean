import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroMemFractionalIdealNormSqLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal

namespace GlobalTheory

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

set_option backward.isDefEq.respectTransparency.types false in

theorem covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)

end Lattice

end GlobalTheory
