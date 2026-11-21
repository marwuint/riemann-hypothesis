import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

noncomputable section

namespace GlobalTheory.RowLev.GroupAlgPos

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

variable {Q : Type} [Group Q]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (q : Q) :
    (a * b).coeff q = ∑ x, a.coeff x * b.coeff (x⁻¹ * q) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))

theorem adj_coeff [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl

theorem adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by
  haveI := Fintype.ofFinite Q
  ext q
  rw [adj_coeff, coeff_mul_eq_sum, coeff_mul_eq_sum, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun x => ?_
  simp [adj_coeff, mul_comm, mul_assoc]

theorem adj_adj [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]

theorem adj_sub [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a - b) = adj a - adj b := by
  ext q; simp [adj_coeff]

theorem isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this

theorem coeff_mul_adj_one [Fintype Q] (a : MonoidAlgebra ℂ Q) :
    (a * adj a).coeff 1 = ∑ x, a.coeff x * star (a.coeff x) := by
  rw [coeff_mul_eq_sum]
  simp only [adj_coeff, mul_one, inv_inv]

theorem eq_zero_of_coeff_mul_adj [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this

theorem isSA_central [Finite Q] (z : MonoidAlgebra ℂ Q) (hz : z * z = z) (hc : ∀ a, z * a = a * z) : IsSA z := by
  have hs : adj z * adj z = adj z := by rw [← adj_mul, hz]
  have h0 : z - z * adj z = 0 := by
    apply eq_zero_of_coeff_mul_adj
    rw [adj_sub, adj_mul, adj_adj]
    have e1 : z * adj z * adj z = z * adj z := by rw [mul_assoc, hs]
    have e2 : z * (z * adj z) = z * adj z := by rw [← mul_assoc, hz]
    have e3 : z * adj z * (z * adj z) = z * adj z := by
      rw [mul_assoc, ← mul_assoc (adj z), ← hc (adj z), mul_assoc z (adj z), hs, e2]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]; simp
  have h1 : z = z * adj z := sub_eq_zero.1 h0
  rw [isSA_iff]
  conv_lhs => rw [h1, adj_mul, adj_adj]
  exact h1.symm

end GlobalTheory.RowLev.GroupAlgPos
