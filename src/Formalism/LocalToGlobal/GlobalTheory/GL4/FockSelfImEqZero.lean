import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingLinkFamilyNormalised
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

theorem fock_eq_sum_coeff {σ : Type} (f g : MvPolynomial σ ℂ) (t : Finset (σ →₀ ℕ)) (ht : f.support ⊆ t) :
    fockF f g = ∑ m ∈ t, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset ht
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fockF_add_left_g_l4 {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fock_eq_sum_coeff (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_coeff f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_coeff f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fock_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : fockF g f = star (fockF f g) := by
  classical
  rw [fock_eq_sum_coeff g f (f.support ∪ g.support) Finset.subset_union_right,
    fock_eq_sum_coeff f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [star_mul', star_mul', star_star, star_natCast]
  ring

theorem fockF_add_right_g_l4 {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_left' {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [fock_eq_sum_coeff (c • f) g f.support MvPolynomial.support_smul]
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_smul_right_eq_star_mul {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fock_self_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockF f f).re := by
  by_cases hf : f = 0
  · subst hf
    unfold fockF
    simp
  · exact (Formalism.GradedWeylDivisibility.fockPos σ f hf).1.le

def fockLin {σ : Type} (G : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun F := fockF F G
  map_add' F F' := fockF_add_left_g_l4 F F' G
  map_smul' c F := by rw [fockF_smul_left', smul_eq_mul, RingHom.id_apply]

def FockSp (σ : Type) : Type := MvPolynomial σ ℂ

instance (σ : Type) : AddCommGroup (FockSp σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))
instance (σ : Type) : Module ℂ (FockSp σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

instance fockCore (σ : Type) : InnerProductSpace.Core ℂ (FockSp σ) where
  inner f g := fockF (show MvPolynomial σ ℂ from g) (show MvPolynomial σ ℂ from f)
  conj_inner_symm x y := by
    show (starRingEnd ℂ) (fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from y)) =
      fockF (show MvPolynomial σ ℂ from y) (show MvPolynomial σ ℂ from x)
    rw [starRingEnd_apply, ← fock_conj_symm]
  re_inner_nonneg x := fock_self_re_nonneg (show MvPolynomial σ ℂ from x)
  add_left x y z := fockF_add_right_g_l4 (show MvPolynomial σ ℂ from z) (show MvPolynomial σ ℂ from x)
    (show MvPolynomial σ ℂ from y)
  smul_left x y r := by
    show fockF (show MvPolynomial σ ℂ from y) (r • (show MvPolynomial σ ℂ from x)) = _
    rw [fockF_smul_right_eq_star_mul, starRingEnd_apply]
  definite x hx := by
    by_contra hne
    have h := (Formalism.GradedWeylDivisibility.fockPos σ (show MvPolynomial σ ℂ from x) hne).1
    have h0 : fockF (show MvPolynomial σ ℂ from x) (show MvPolynomial σ ℂ from x) = 0 := hx
    rw [h0, Complex.zero_re] at h
    exact lt_irrefl _ h

instance (σ : Type) : NormedAddCommGroup (FockSp σ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (FockSp σ) _ _ _ (fockCore σ)

instance (σ : Type) : InnerProductSpace ℂ (FockSp σ) := InnerProductSpace.ofCore (fockCore σ).toCore

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
