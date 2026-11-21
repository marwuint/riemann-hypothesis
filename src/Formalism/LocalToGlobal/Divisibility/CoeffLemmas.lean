import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Formalism.LocalToGlobal.UnitaryNorms.PowValCast

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

theorem exists_sqrt (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩

theorem sqrts_sub (m : ℤ) : sqrts m ⊆ (sqQ m : Set Qb) := subset_adjoin ℚ _

theorem isAlgebraicQb (LL : Fld) : Algebra.IsAlgebraic LL Qb := by
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) LL

theorem exists_ext (ι : Qb →+* ℂ) (LL : Fld) (σ : CoF ι LL →+* ℂ) :
    ∃ τ : Qb →+* ℂ, ∀ x : CoF ι LL, τ (CoF.val ι LL x) = σ x := by
  have := isAlgebraicQb LL
  let f : LL →ₐ[ℚ] ℂ := RingHom.toRatAlgHom (R := LL) σ
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f
  refine ⟨φ.toRingHom, fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

end Formalism.L2.DIV
