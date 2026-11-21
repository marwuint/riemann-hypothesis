import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FderivFderivLogRho
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace P1

abbrev Fld : Type := FractionRing (Polynomial ℤ)

instance : CharZero Fld :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (Polynomial ℤ) Fld)

instance (priority := 10000) fldAlgInt : Algebra ℤ Fld := Ring.toIntAlgebra Fld

abbrev J2 : Type := Ix (Fin 2)

def p0 : J2 := ⟨(), 0⟩

def p1 : J2 := ⟨(), 1⟩

def val (q : J2) : Polynomial ℤ := if q.2 = 0 then 1 else Polynomial.X

def x : J2 → Fld := fun q ↦ algebraMap (Polynomial ℤ) Fld (val q)

theorem isSmoothHerm_fs {κ : Type} [Fintype κ] : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix κ))) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FSLevi.nsq (J := Ix κ)) := by
    unfold FSLevi.nsq
    exact ContDiff.sum fun p _ ↦ ((FSLevi.reP p).contDiff.pow 2).add ((FSLevi.imaginary p).contDiff.pow 2)
  have he : (HermLine.ofCone (fsMetric (Ix κ))).h = fun z ↦ Real.sqrt (FSLevi.nsq z) := by
    funext z
    simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply,
      FSLevi.imaginaryPart_apply, FSLevi.norm_sq_eq]
  unfold IsSmoothHerm
  rw [he]
  refine hN.contDiffOn.sqrt fun z hz ↦ (FSLevi.nsq_pos ?_).ne'
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 ↦ hi (congrFun h0 _)

end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
