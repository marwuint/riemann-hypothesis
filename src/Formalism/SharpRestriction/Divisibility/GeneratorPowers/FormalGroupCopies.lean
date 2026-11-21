import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv R (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

end Formalism.MainNotions.ModuliIntegralCharts.H1
