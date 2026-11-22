import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FracZeroOfPos

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR
open scoped TensorProduct

namespace GlobalTheory.W1

variable {K L : Type} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]

structure IsProdField (i1 i2 : K →ₐ[ℂ] L) : Prop where
  inj : Function.Injective (Algebra.TensorProduct.productMap i1 i2)
  gen : IntermediateField.adjoin ℂ (Set.range i1 ∪ Set.range i2) = ⊤

def prDR (i : K →ₐ[ℂ] L) : DR ℂ K →+* DR ℂ L :=
  letI : Algebra K L := i.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (i.commutes c).symm
  (mapDR ℂ K L).toRingHom

def prodRing (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : Subalgebra ℂ L := Algebra.adjoin ℂ (i1 '' B ∪ i2 '' B)

def prodMap (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : B ⊗[ℂ] B →ₐ[ℂ] L :=
  Algebra.TensorProduct.productMap (i1.comp B.val) (i2.comp B.val)

theorem range_prodMap (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : (prodMap i1 i2 B).range = prodRing i1 i2 B := by
  rw [prodMap, Algebra.TensorProduct.productMap_range, prodRing, Algebra.adjoin_union, AlgHom.range_comp, AlgHom.range_comp,
    Subalgebra.range_val, ← Subalgebra.coe_map, ← Subalgebra.coe_map, Algebra.adjoin_eq, Algebra.adjoin_eq]

theorem IsProdField.prodMap_injective {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) :
    Function.Injective (prodMap i1 i2 B) := by
  have e : prodMap i1 i2 B =
      (Algebra.TensorProduct.productMap i1 i2).comp (Algebra.TensorProduct.map B.val B.val) := by
    ext <;> simp [prodMap]
  rw [e, AlgHom.coe_comp]
  exact hP.inj.comp (TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
    Subtype.val_injective Subtype.val_injective)

def IsProdField.prodEquiv {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) :
    B ⊗[ℂ] B ≃ₐ[ℂ] prodRing i1 i2 B :=
  (AlgEquiv.ofInjective _ (hP.prodMap_injective B)).trans (Subalgebra.equivOfEq _ _ (range_prodMap i1 i2 B))

def diagForm (i1 i2 : K →ₐ[ℂ] L) {d : ℕ} (t : Fin d → K) (a : ℕ) : DR ℂ L :=
  ∑ S ∈ Finset.univ.powersetCard a, (List.ofFn fun l : Fin d =>
    if l ∈ S then prDR i1 (ExteriorAlgebra.ι K (D ℂ K (t l))) else -prDR i2 (ExteriorAlgebra.ι K (D ℂ K (t l)))).prod

structure IsEtFrame (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) : Prop where
  indep : LinearIndependent K (fun l => D ℂ K (t l))
  comb : ∀ b ∈ B, ∃ c : Fin d → K, (∀ l, c l ∈ B) ∧ D ℂ K b = ∑ l, c l • D ℂ K (t l)
  frac : IsFractionRing B K

def IsEtCoord (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) : Prop :=
  (∀ l, t l ∈ B) ∧ IsEtFrame B t

theorem IsEtCoord.span_eq_top {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Submodule.span K (Set.range fun l => D ℂ K (t l)) = ⊤ := by
  haveI := ht.2.frac
  have hB : ∀ b : B, D ℂ K (algebraMap B K b) ∈ Submodule.span K (Set.range fun l => D ℂ K (t l)) := by
    intro b
    obtain ⟨c, -, hc⟩ := ht.2.2 b b.2
    rw [show algebraMap B K b = (b : K) from rfl, hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [SetLike.mem_coe, Derivation.leibniz_div]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ (hB a)) (Submodule.smul_mem _ _ (hB b)))

def IsEtCoord.basis {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Module.Basis (Fin d) K Ω[K⁄ℂ] := Module.Basis.mk ht.2.1 ht.span_eq_top.ge

theorem IsEtCoord.finrank_eq {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Module.finrank K Ω[K⁄ℂ] = d := by
  rw [Module.finrank_eq_card_basis ht.basis, Fintype.card_fin]

namespace Aff

abbrev Fn (d : ℕ) : Type := FractionRing (MvPolynomial (Fin d) ℂ)

def coord (d : ℕ) : Fin d → Fn d := fun l => algebraMap (MvPolynomial (Fin d) ℂ) (Fn d) (MvPolynomial.X l)

abbrev polyRing (d : ℕ) : Subalgebra ℂ (Fn d) := Algebra.adjoin ℂ (Set.range (coord d))

theorem algebraMap_mem (d : ℕ) (p : MvPolynomial (Fin d) ℂ) : algebraMap _ (Fn d) p ∈ polyRing d := by
  induction p using MvPolynomial.induction_on with
  | C c => exact (polyRing d).algebraMap_mem c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p l hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨l, rfl⟩)

instance isFractionRing (d : ℕ) : IsFractionRing (polyRing d) (Fn d) :=
  IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) ℂ) z
    exact ⟨⟨_, algebraMap_mem d a⟩, ⟨_, algebraMap_mem d b⟩, rfl⟩

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let F := FractionRing P
  letI : Algebra (P ⊗[k] A) (F ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P F) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (F ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) F
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (F ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

instance isDomain_tensor_self (d : ℕ) : IsDomain (Fn d ⊗[ℂ] Fn d) := isDomain_tensor ℂ (Fin d) (Fn d)

end Aff

end GlobalTheory.W1
