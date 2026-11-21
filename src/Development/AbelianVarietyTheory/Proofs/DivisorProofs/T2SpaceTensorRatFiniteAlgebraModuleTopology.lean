import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

open NumberField Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.LKTrip

namespace LevelExists

theorem isCompact_intCompl (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  haveI : CompleteSpace (v.adicCompletionIntegers ℚ) :=
    (Valued.isClosed_valuationSubring (v.adicCompletion ℚ)).completeSpace_coe
  haveI : Finite (ℤ ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  have hc : CompactSpace (Valued.integer (v.adicCompletion ℚ)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨inferInstanceAs (CompleteSpace (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))⟩
  exact isCompact_iff_compactSpace.mpr hc

def rp {p : ℕ} (x : AfP p) : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] := x

def intAfP (p : ℕ) : Subring (AfP p) where
  carrier := {x | ∀ v : AwayP p, (rp x).1 v ∈ v.1.adicCompletionIntegers ℚ}
  mul_mem' := by intro a b ha hb v; exact mul_mem (ha v) (hb v)
  one_mem' := by intro v; exact one_mem _
  add_mem' := by intro a b ha hb v; exact add_mem (ha v) (hb v)
  zero_mem' := by intro v; exact zero_mem _
  neg_mem' := by intro a ha v; exact neg_mem (ha v)

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p : Set (AfP p)) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
    (fun w => Valued.isOpen_valuationSubring (w.1.adicCompletion ℚ))

theorem isCompact_intAfP (p : ℕ) : IsCompact (intAfP p : Set (AfP p)) := by
  haveI : ∀ w : AwayP p, CompactSpace (w.1.adicCompletionIntegers ℚ) :=
    fun w => isCompact_iff_compactSpace.mp (isCompact_intCompl w.1)
  let e := RestrictedProduct.homeoTop (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
  let f : (Π w : AwayP p, w.1.adicCompletionIntegers ℚ) → AfP p := fun g =>
    RestrictedProduct.inclusion (fun w : AwayP p => w.1.adicCompletion ℚ)
      (fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ))) le_top (e g)
  have hf : Continuous f :=
    (RestrictedProduct.continuous_inclusion le_top).comp e.continuous
  have hset : (intAfP p : Set (AfP p)) = Set.range f := by
    ext x
    constructor
    · intro hx
      exact ⟨fun w => ⟨(rp x).1 w, hx w⟩, rfl⟩
    · rintro ⟨g, rfl⟩ w
      exact (g w).2
  rw [hset]
  exact isCompact_range hf

end LevelExists

namespace LevelExists

section Tensor

variable (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
  (F : Type) [Field F] [NumberField F]

def tensorInt (O : Subring R) : Subring (R ⊗[ℚ] F) where
  carrier := {x | ∀ i j, Algebra.leftMulMatrix (Algebra.TensorProduct.basis R (Module.finBasis ℚ F)) x i j ∈ O}
  mul_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hx i k) (hy k j)
  one_mem' := by
    intro i j
    simp only [Set.mem_setOf_eq, map_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro x hx i j
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

def mulMatAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    R ⊗[ℚ] A →ₐ[R] Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R :=
  (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R (Module.finBasis ℚ A))).toAlgHom.comp
    (Algebra.lmul R (R ⊗[ℚ] A))

theorem t2Space_tensor_rat_finite_algebra_moduleTopology [T2Space R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    @T2Space (R ⊗[ℚ] A) (moduleTopology R (R ⊗[ℚ] A)) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  haveI : IsModuleTopology R (R ⊗[ℚ] A) := ⟨rfl⟩
  set bS := Algebra.TensorProduct.basis R (Module.finBasis ℚ A)
  exact T2Space.of_injective_continuous bS.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap bS.equivFun.toLinearMap)

end Tensor

end LevelExists

namespace LevelExists

end LevelExists

end GlobalTheory.LKTrip
